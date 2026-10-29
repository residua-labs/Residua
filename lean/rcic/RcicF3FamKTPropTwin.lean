/-
The Prop twin of the `famLim ↔ famKT` bridge (`RcicF3FamKTBridge`).

The Type twin (`famLim_famKT_type`) covers only `famKT`'s `≠ 0` branch; the
Prop-read half was the named residue `[rcic-f3-famkt-bridge-prop-twin]`.
This module closes it:

* `ctorFitsStage n σ ps is` — the stage-`n` Prop-fibre truth: some
  constructor fits at the iterate table `tabIter n` with result indices `is`.
* `limEnd_famEndP` — at a Prop-read result level, the limit end is the
  `famEndP` truth: `(∃ n, ctorFitsStage n) ↔ (tup is ∈ DStarP)`.
  * `dstarP_of_ctorFitsStage` (⇒): stage induction; every recursive field's
    `Ed`-read at stage `n + 1` unfolds (via `ed_rec_succ_fit`) to the stage-`n`
    fibre truth, which the IH ships into `DStarP`; the surviving telescope
    re-reads as `TelFitsP` at `DStarP`, and `DStarP_isLfp`'s closure gives
    membership.
  * `ctorFitsStage_of_dstarP` (⇐): `lfp_induction` on `PhiP` (`PhiP_ktop`);
    the stage property is post-fixed because a `TelFitsP`-witness's recursive
    fields carry strictly-earlier stages, and `ed_rec_succ_fit` rebuilds the
    `TelFits` read at the next stage (`ctorFitsStage_succ` lifts within the
    walk).
* `famLim_famLfpP` / `famLim_famKT_prop` — the entry-level twins
  (`piLam_congr_fits₂` over the pointwise fibre equivalence), the Prop-read
  mirror of `famLim_famLfp` / `famLim_famKT_type`.

Premises: the Type twin's `hB hpf hri hres hnoFn` plus `hclsA`
(`FieldsClassA`, the `PropFix` form) instead of the raw `FieldsClass`;
`hnoFn` kills the `FnRec` arm exactly as in the Type twin (the
`[rcic-f3-famkt-bridge-fn-cont]` refutation shows it is witness-necessary
there; here it is the same gate).  `NonIRSem` is NOT needed on this route.

closure_claim = 0.
-/

import rcic.RcicF3FamKTBridge
import rcic.RcicF3KTWPropFix
import rcic.RcicF3StepAG

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

section PropTwin

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hclsA : ∀ c, c ∈ fd.ctors →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
  (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)
  (hnoFn : ∀ c, c ∈ fd.ctors → ∀ p, p ∈ kindsOf fd.fref c.1 → p ≠ PKind.fn)

/-! ### plumbing -/

/-- The union of truth values is the truth of the existential. -/
theorem iUnionN_tv {φ : Nat → Prop} :
    Equiv (iUnionN fun n => tv (φ n)) (tv (∃ n, φ n)) := by
  refine ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
    exact mem_tv.mpr ⟨⟨n, (mem_tv.mp hn).1⟩, (mem_tv.mp hn).2⟩
  · obtain ⟨n, hn⟩ := (mem_tv.mp hz).1
    exact mem_iUnionN.mpr ⟨n, mem_tv.mpr ⟨hn, (mem_tv.mp hz).2⟩⟩

include hclsA hnoFn in
/-- The `RecApp`-form field premise of the chain lemmas, from class-A plus
`hnoFn` (`fieldsClass_of_classA_noFn` kills the `FnRec` arm;
`recApp_of_directRec` re-reads the `DirectRec` arm). -/
theorem hclsRec_of_classA (c) (hc : c ∈ fd.ctors) : ∀ A, A ∈ c.1 →
    occursConst fd.fref A = false ∨ RecApp fd ar A := by
  intro A hA
  rcases FieldsClass.mem
    (StepAG.fieldsClass_of_classA_noFn fd.fref ar fd.params.length fd.indices.length c.1 0
      (fun A' hA' hkind =>
        (hnoFn c hc _ (List.mem_map.mpr ⟨A', hA', hkind⟩)) rfl)
      (hclsA c hc)) A hA with h | ⟨d, hd⟩
  · exact Or.inl h
  · exact Or.inr (StepAG.recApp_of_directRec rfl rfl hd)

/-! ### the stage truth -/

/-- The stage-`n` Prop-fibre truth at params `ps`, indices `is`: some
constructor's fields fit at the iterate table `tabIter n`. -/
def ctorFitsStage (n : Nat) (σ : Nat → Nat) (ps is : List PSet.{4}) : Prop :=
  ∃ j xs, CtorFits (mkM P (tabIter P μ fd n)) σ fd.ctors (push ps ρ0) is j xs

variable {P μ fd}

/-- The Prop-read stage end, normalized at a split environment. -/
theorem famEnd_propStage (σ : Nat → Nat) (ps is : List PSet.{4})
    (his : is.length = fd.indices.length)
    (hk : evalTotal σ fd.resLevel = 0) (n : Nat) :
    famEnd (mkM P (tabIter P μ fd n)) W4 σ fd (push (ps ++ is) ρ0) =
      tyv (tv (ctorFitsStage P μ fd n σ ps is)) := by
  have hsplit : push (ps ++ is) ρ0 = push is (push ps ρ0) :=
    push_append ps is ρ0
  rw [hsplit]
  show famEnd _ W4 σ fd _ = _
  unfold famEnd
  rw [cond_pos hk]
  show tyv (PropFib (mkM P (tabIter P μ fd n)) σ fd.ctors _ _) = _
  rw [← his, shiftρ_push, lastVals_push]
  unfold PropFib ctorFitsStage
  rfl

include hB in
/-- The Prop-read limit end is the truth of the stage disjunction. -/
theorem limEnd_propStage (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length) (his : is.length = fd.indices.length)
    (hk : evalTotal σ fd.resLevel = 0) :
    Equiv (limEnd P μ fd σ (push (ps ++ is) ρ0))
      (tyv (tv (∃ n, ctorFitsStage P μ fd n σ ps is))) := by
  refine tyv_congr ((iUnionN_congr fun n => ?_).trans iUnionN_tv)
  have e := famEnd_propStage (P := P) (μ := μ) σ ps is his hk n
  rw [e]
  exact el_tyv


/-! ### §3 field-kind plumbing -/

/-- No field of a `.fn`-free telescope has kind `.fn`. -/
theorem hnoFn_of_mem (Fs : List (Expr Nat)) :
    (∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn) →
    ∀ (d : Nat) (A : Expr Nat),
    FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs d → A ∈ Fs →
    kindOf fd.fref A ≠ PKind.fn :=
  fun hnf _ A _ hA hkind => hnf _ (List.mem_map.mpr ⟨A, hA, hkind⟩) rfl

/-! ### §4 stage monotonicity -/

include hB hpf hclsA hri hnoFn in
/-- The recursive spine's `Ed` grows along the iterate chain. -/
theorem ed_iter_lift (k k' : Nat) (hkk' : k ≤ k') (σ : Nat → Nat) (ρ : Nat → PSet.{4})
    (args : List (Expr Nat)) (hargs : ∀ e, e ∈ args → occursConst fd.fref e = false)
    (hl : args.length = (fd.params ++ fd.indices).length) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P (tabIter P μ fd k))
      (den (mkM P (tabIter P μ fd k)) σ ρ (foldApps (.const fd.fref (canonL ar)) args))) :
    z ∈ Ed (mkM P (tabIter P μ fd k'))
      (den (mkM P (tabIter P μ fd k')) σ ρ (foldApps (.const fd.fref (canonL ar)) args)) := by
  induction hkk' with
  | refl => exact hz
  | @step m h ih =>
      exact rec_iter_mono P μ fd ar hB hpf
        (hclsRec_of_classA fd ar hclsA hnoFn) hri m σ ρ args hargs hl z ih

include hB hpf hclsA hri hnoFn in
/-- A class-A telescope's `TelFits` read grows along the iterate chain. -/
theorem telFits_iter_lift (k k' : Nat) (hkk' : k ≤ k') (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) :
    ∀ (Fs : List (Expr Nat)) (pre xs : List PSet.{4}),
    (∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn) →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs pre.length →
    TelFits (mkM P (tabIter P μ fd k)) σ Fs (push pre (push ps ρ0)) xs →
    TelFits (mkM P (tabIter P μ fd k')) σ Fs (push pre (push ps ρ0)) xs := by
  intro Fs
  induction Fs with
  | nil => intro pre xs _ _ h; cases xs with
    | nil => exact h
    | cons x xs' => exact False.elim h
  | cons A Fs ih =>
      intro pre xs hnf hcl h
      obtain ⟨hdisj, hcl'⟩ := hcl
      have hnf' : ∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn := by
        intro p hp; exact hnf p (List.mem_cons_of_mem (kindOf fd.fref A) hp)
      cases xs with
      | nil => exact False.elim h
      | cons x xs' =>
          obtain ⟨hx, hrest⟩ := h
          have hcons : vcons x (push pre (push ps ρ0)) =
              push (pre ++ [x]) (push ps ρ0) :=
            (push_append pre [x] (push ps ρ0)).symm
          rw [hcons] at hrest
          have hih := ih (pre ++ [x]) xs' hnf' (by simp; exact hcl') hrest
          rw [← hcons] at hih
          refine ⟨?_, hih⟩
          rcases hdisj with hfree | hd | hfn
          · unfold tabIter at hx ⊢
            rw [den_off P μ fd.fref (famIter P μ fd k) σ _ hfree] at hx
            rw [den_off P μ fd.fref (famIter P μ fd k') σ _ hfree]
            rw [ed_mkM P (upd μ fd.fref (famIter P μ fd k))
              (upd μ fd.fref (famIter P μ fd k'))] at hx
            exact hx
          · obtain ⟨idx, hAe, hidx, hfree⟩ := hd
            have hargs : ∀ e, e ∈ policyParameterLocals fd.params.length pre.length ++ idx →
                occursConst fd.fref e = false := by
              intro e he
              rcases List.mem_append.mp he with hm | hm
              · exact paramLocals_free fd.fref fd.params.length pre.length e hm
              · exact hfree e hm
            have hl : (policyParameterLocals fd.params.length pre.length ++ idx).length =
                (fd.params ++ fd.indices).length := by
              simp only [List.length_append, length_paramLocals, hidx]
            rw [hAe] at hx ⊢
            exact ed_iter_lift (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn k k'
              hkk' σ (push pre (push ps ρ0)) _ hargs hl x hx
          · exact absurd rfl (hnf _ (List.mem_map.mpr ⟨A, by simp, kindOf_fnRec hfn⟩))

include hB hpf hclsA hri hnoFn in
/-- The stage truth grows along the chain. -/
theorem ctorFitsStage_succ (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length) (n : Nat)
    (h : ctorFitsStage P μ fd n σ ps is) :
    ctorFitsStage P μ fd (n + 1) σ ps is := by
  obtain ⟨j, xs, c', hc', htf, hle⟩ := h
  have hcm : c' ∈ fd.ctors := List.getElem?_mem hc'
  have hden : c'.2.map (den (mkM P (tabIter P μ fd (n + 1))) σ (push xs (push ps ρ0))) =
      c'.2.map (den (mkM P (tabIter P μ fd n)) σ (push xs (push ps ρ0))) := by
    refine List.map_congr_left fun e he => ?_
    show den (mkM P (upd μ fd.fref (famIter P μ fd (n + 1)))) σ _ e =
      den (mkM P (upd μ fd.fref (famIter P μ fd n))) σ _ e
    rw [den_off P μ fd.fref (famIter P μ fd (n + 1)) σ _ (hri c' hcm e he),
      den_off P μ fd.fref (famIter P μ fd n) σ _ (hri c' hcm e he)]
  refine ⟨j, xs, c', hc', ?_, hden ▸ hle⟩
  exact telFits_iter_lift (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn
    n (n + 1) (Nat.le_succ n) σ ps hps
    c'.1 [] xs (fun p hp => hnoFn c' hcm p hp) (hclsA c' hcm) htf

/-! ### §5 the ⇒ direction: stage truth ⇒ `DStarP` -/

include hB hpf hclsA hri hnoFn in
/-- The base walk: a stage-`0` `TelFits` read re-reads as `TelFitsP` at any
`T` (all recursive fields die: the stage-`0` spine `Ed` is empty). -/
theorem telFitsP_of_telFits_zero (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) (T : PSet.{4}) :
    ∀ (Fs : List (Expr Nat)) (pre xs : List PSet.{4}),
    (∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn) →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs pre.length →
    TelFits (mkM P (tabIter P μ fd 0)) σ Fs (push pre (push ps ρ0)) xs →
    TelFitsP P μ fd T σ Fs (push pre (push ps ρ0)) xs := by
  intro Fs
  induction Fs with
  | nil => intro pre xs _ _ h; cases xs with
    | nil => exact h
    | cons x xs' => exact False.elim h
  | cons A Fs ih =>
      intro pre xs hnf hcl h
      obtain ⟨hdisj, hcl'⟩ := hcl
      have hnf' : ∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn := by
        intro p hp; exact hnf p (List.mem_cons_of_mem (kindOf fd.fref A) hp)
      cases xs with
      | nil => exact False.elim h
      | cons x xs' =>
          obtain ⟨hx, hrest⟩ := h
          have hcons : vcons x (push pre (push ps ρ0)) =
              push (pre ++ [x]) (push ps ρ0) :=
            (push_append pre [x] (push ps ρ0)).symm
          rw [hcons] at hrest
          have hih := ih (pre ++ [x]) xs' hnf' (by simp; exact hcl') hrest
          rw [← hcons] at hih
          refine ⟨?_, hih⟩
          rcases hdisj with hfree | hd | hfn
          · show okP P μ fd T σ (push pre (push ps ρ0)) A x
            unfold tabIter at hx
            rw [den_off P μ fd.fref (famIter P μ fd 0) σ _ hfree] at hx
            rw [ed_mkM P (upd μ fd.fref (famIter P μ fd 0)) μ] at hx
            simp only [okP]
            cases hk2 : kindOf fd.fref A with
            | plain => exact hx
            | direct => exact absurd hk2 (by
                rw [kindOf_free hfree]; exact fun h => PKind.noConfusion h)
            | fn => exact absurd hk2 (by
                rw [kindOf_free hfree]; exact fun h => PKind.noConfusion h)
          · obtain ⟨idx, hAe, hidx, hfree⟩ := hd
            have hargs : ∀ e, e ∈ policyParameterLocals fd.params.length pre.length ++ idx →
                occursConst fd.fref e = false := by
              intro e he
              rcases List.mem_append.mp he with hm | hm
              · exact paramLocals_free fd.fref fd.params.length pre.length e hm
              · exact hfree e hm
            have hl : (policyParameterLocals fd.params.length pre.length ++ idx).length =
                (fd.params ++ fd.indices).length := by
              simp only [List.length_append, length_paramLocals, hidx]
            rw [hAe] at hx
            exact absurd (mem_congr_right
              (ed_rec_zero P μ fd ar hB hpf σ (push pre (push ps ρ0)) _ hargs hl) hx)
              not_mem_pempty
          · exact absurd rfl (hnf _ (List.mem_map.mpr ⟨A, by simp, kindOf_fnRec hfn⟩))

include hB hpf hclsA hri hnoFn in
/-- The step walk: a stage-`n+1` `TelFits` read re-reads as `TelFitsP` at
`DStarP`, under the stage-`n` induction hypothesis. -/
theorem telFitsP_of_telFits_succ (n : Nat) (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (hk : evalTotal σ fd.resLevel = 0)
    (IH : ∀ is, TelFits (mkM P μ) σ fd.indices (push ps ρ0) is →
      ctorFitsStage P μ fd n σ ps is →
      tup is ∈ DStarP P μ fd σ (push ps ρ0)) :
    ∀ (Fs : List (Expr Nat)) (pre xs : List PSet.{4}),
    (∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn) →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs pre.length →
    TelFits (mkM P (tabIter P μ fd (n + 1))) σ Fs (push pre (push ps ρ0)) xs →
    TelFitsP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ Fs (push pre (push ps ρ0)) xs := by
  intro Fs
  induction Fs with
  | nil => intro pre xs _ _ h; cases xs with
    | nil => exact h
    | cons x xs' => exact False.elim h
  | cons A Fs ih =>
      intro pre xs hnf hcl h
      obtain ⟨hdisj, hcl'⟩ := hcl
      have hnf' : ∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn := by
        intro p hp; exact hnf p (List.mem_cons_of_mem (kindOf fd.fref A) hp)
      cases xs with
      | nil => exact False.elim h
      | cons x xs' =>
          obtain ⟨hx, hrest⟩ := h
          have hcons : vcons x (push pre (push ps ρ0)) =
              push (pre ++ [x]) (push ps ρ0) :=
            (push_append pre [x] (push ps ρ0)).symm
          rw [hcons] at hrest
          have hih := ih (pre ++ [x]) xs' hnf' (by simp; exact hcl') hrest
          rw [← hcons] at hih
          refine ⟨?_, hih⟩
          rcases hdisj with hfree | hd | hfn
          · show okP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ
              (push pre (push ps ρ0)) A x
            unfold tabIter at hx
            rw [den_off P μ fd.fref (famIter P μ fd (n + 1)) σ _ hfree] at hx
            rw [ed_mkM P (upd μ fd.fref (famIter P μ fd (n + 1))) μ] at hx
            simp only [okP]
            cases hk2 : kindOf fd.fref A with
            | plain => exact hx
            | direct => exact absurd hk2 (by
                rw [kindOf_free hfree]; exact fun h => PKind.noConfusion h)
            | fn => exact absurd hk2 (by
                rw [kindOf_free hfree]; exact fun h => PKind.noConfusion h)
          · obtain ⟨idx, hAe, hidx, hfree⟩ := hd
            have hargs : ∀ e, e ∈ policyParameterLocals fd.params.length pre.length ++ idx →
                occursConst fd.fref e = false := by
              intro e he
              rcases List.mem_append.mp he with hm | hm
              · exact paramLocals_free fd.fref fd.params.length pre.length e hm
              · exact hfree e hm
            have hl : (policyParameterLocals fd.params.length pre.length ++ idx).length =
                (fd.params ++ fd.indices).length := by
              simp only [List.length_append, length_paramLocals, hidx]
            rw [hAe] at hx ⊢
            simp only [okP]
            cases hk2 : kindOf fd.fref (foldApps (.const fd.fref (canonL ar))
                (policyParameterLocals fd.params.length pre.length ++ idx)) with
            | plain => exact absurd hk2 (by
                have hkd := kindOf_directRec ⟨idx, hAe, hidx, hfree⟩
                rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)
            | direct =>
                rw [familyIdx_directRec]
                refine @Decidable.byCases _ _
                  (P.dec (RecFits P μ fd σ (push pre (push ps ρ0))
                    (policyParameterLocals fd.params.length pre.length ++ idx)))
                  (fun hfit => ?_) (fun hnf => ?_)
                · have hmap : (policyParameterLocals fd.params.length pre.length ++ idx).map
                      (den (mkM P μ) σ (push pre (push ps ρ0))) =
                      ps ++ idx.map (den (mkM P μ) σ (push pre (push ps ρ0))) := by
                    rw [List.map_append]
                    have he : push (ps ++ pre) ρ0 = push pre (push ps ρ0) :=
                      push_append ps pre ρ0
                    congr 1
                    rw [← hps]
                    have hd := den_paramLocals (mkM P μ) σ ps pre ρ0
                    rw [he] at hd
                    exact hd
                  have e1 := ed_rec_succ_fit P μ fd ar hB hpf n σ
                    (push pre (push ps ρ0)) _ hargs hfit
                  rw [hmap] at e1
                  have hx1 : x ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 σ fd
                      (push (ps ++ idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) ρ0)) :=
                    mem_congr_right e1 hx
                  have hidxv : (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))).length =
                      fd.indices.length := (List.length_map _ _).trans hidx
                  have e2 := famEnd_propStage (P := P) (μ := μ) σ ps _ hidxv hk n
                  rw [e2] at hx1
                  have hx2 : x ∈ tv (ctorFitsStage P μ fd n σ ps
                      (idx.map (den (mkM P μ) σ (push pre (push ps ρ0))))) :=
                    mem_congr_right el_tyv hx1
                  obtain ⟨hφ, hxp⟩ := mem_tv.mp hx2
                  have htf' : TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
                      ((policyParameterLocals fd.params.length pre.length ++ idx).map
                        (den (mkM P μ) σ (push pre (push ps ρ0)))) := hfit
                  rw [hmap] at htf'
                  obtain ⟨ps₂, is₂, hsp, hps2T, his2⟩ :=
                    TelFits_split fd.params fd.indices ρ0 _ htf'
                  have hlen : ps₂.length = ps.length :=
                    (TelFits.length hps2T).trans hps.symm
                  obtain ⟨hps2, his2v⟩ := List.append_inj hsp hlen.symm
                  rw [← hps2, ← his2v] at his2
                  exact ⟨hxp, (argsFitF_directRec P μ fd σ (push pre (push ps ρ0)) fd.fref
                    (canonL ar) _).mpr hfit, IH _ his2 hφ⟩
                · exact absurd (mem_congr_right
                    (ed_rec_succ_nofit P μ fd ar hB hpf n σ (push pre (push ps ρ0)) _ hargs
                      hl hnf) hx) not_mem_pempty
            | fn => exact absurd hk2 (by
                have hkd := kindOf_directRec ⟨idx, hAe, hidx, hfree⟩
                rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)
          · exact absurd rfl (hnf _ (List.mem_map.mpr ⟨A, by simp, kindOf_fnRec hfn⟩))

include hri hres in
/-- The `PhiP` packaging: a `TelFitsP` witness at `DStarP` with index match
gives `DStarP` membership (the closure half of `DStarP_isLfp`). -/
theorem dstarP_of_fits (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (his : TelFits (mkM P μ) σ fd.indices (push ps ρ0) is)
    (n : Nat) (j : Nat) (xs : List PSet.{4}) (c : List (Expr Nat) × List (Expr Nat))
    (hc : fd.ctors[j]? = some c)
    (htfP : TelFitsP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ c.1 (push ps ρ0) xs)
    (hle : LEq (c.2.map (den (mkM P (tabIter P μ fd n)) σ (push xs (push ps ρ0)))) is) :
    tup is ∈ DStarP P μ fd σ (push ps ρ0) := by
  have hcm : c ∈ fd.ctors := List.getElem?_mem hc
  have hresμ : c.2.map (den (mkM P μ) σ (push xs (push ps ρ0))) =
      c.2.map (den (mkM P (tabIter P μ fd n)) σ (push xs (push ps ρ0))) :=
    List.map_congr_left fun e he =>
      (den_off P μ fd.fref (famIter P μ fd n) σ _ (hri c hcm e he)).symm
  have hUP : tup is ∈ UP P μ fd σ (push ps ρ0) :=
    ((mem_FitSetU_iff (mkM P μ) σ fd.indices (push ps ρ0)).mpr ⟨is, Equiv.rfl, his⟩)
  obtain ⟨i, hi⟩ := hUP
  have hmem : tup is ∈ PhiP P μ fd σ (push ps ρ0) (DStarP P μ fd σ (push ps ρ0)) :=
    mem_sep.mpr ⟨i, ⟨j, c, xs, hc, htfP,
      hi.trans ((tup_congr (hresμ ▸ hle)).symm)⟩, hi⟩
  exact (DStarP_isLfp P μ fd σ (push ps ρ0)).1 _ hmem

include hB hpf hclsA hri hres hnoFn in
/-- **⇒**: the stage truth ships into `DStarP` (stage induction). -/
theorem dstarP_of_ctorFitsStage (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (hk : evalTotal σ fd.resLevel = 0) :
    ∀ (n : Nat) (is : List PSet.{4}),
    TelFits (mkM P μ) σ fd.indices (push ps ρ0) is →
    ctorFitsStage P μ fd n σ ps is →
    tup is ∈ DStarP P μ fd σ (push ps ρ0) := by
  intro n
  induction n with
  | zero =>
      intro is his h
      obtain ⟨j, xs, c, hc, htf, hle⟩ := h
      have hcm : c ∈ fd.ctors := List.getElem?_mem hc
      refine dstarP_of_fits (P := P) (μ := μ) (fd := fd) hri hres σ ps is hps his 0 j xs c hc ?_ hle
      exact telFitsP_of_telFits_zero (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn σ ps hps
        (DStarP P μ fd σ (push ps ρ0)) c.1
        [] xs (fun p hp => hnoFn c hcm p hp) (hclsA c hcm) htf
  | succ n ih =>
      intro is his h
      obtain ⟨j, xs, c, hc, htf, hle⟩ := h
      have hcm : c ∈ fd.ctors := List.getElem?_mem hc
      refine dstarP_of_fits (P := P) (μ := μ) (fd := fd) hri hres σ ps is hps his (n + 1) j xs c hc ?_ hle
      exact telFitsP_of_telFits_succ (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn n σ ps hps
        hk ih c.1
        [] xs (fun p hp => hnoFn c hcm p hp) (hclsA c hcm) htf

/-! ### §6 the ⇐ direction: `DStarP` ⇒ stage truth -/

/-- The stage property carried through the leastness induction. -/
def stageQ (σ : Nat → Nat) (ps : List PSet.{4}) (z : PSet.{4}) : Prop :=
  ∃ n is, Equiv z (tup is) ∧ is.length = fd.indices.length ∧
    ctorFitsStage P μ fd n σ ps is

include hB hpf hclsA hri hnoFn in
/-- The stage truth grows along the `≤` chain. -/
theorem ctorFitsStage_le (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length) :
    ∀ {m N : Nat}, m ≤ N → ctorFitsStage P μ fd m σ ps is →
    ctorFitsStage P μ fd N σ ps is := by
  intro m N hle h
  induction hle with
  | refl => exact h
  | @step k hk ih =>
      exact ctorFitsStage_succ (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn σ ps is hps k ih

theorem ctorFitsStage_leq (σ : Nat → Nat) (ps is is' : List PSet.{4})
    (hle : LEq is is') (n : Nat)
    (h : ctorFitsStage P μ fd n σ ps is) :
    ctorFitsStage P μ fd n σ ps is' := by
  obtain ⟨j, xs, c, hc, htf, hle'⟩ := h
  exact ⟨j, xs, c, hc, htf, hle'.trans hle⟩

/-- The `okP`-read of a free field is the base `Ed`-read. -/
theorem okP_plain_inv (T : PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (A : Expr Nat)
    (x : PSet.{4}) (hfree : occursConst fd.fref A = false)
    (h : okP P μ fd T σ ρ A x) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ A) := by
  simp only [okP, kindOf_free hfree] at h
  exact h

/-- The `okP`-read of a `DirectRec` field splits into `∅`-shape, `argsFitF`
and the `T`-membership of the index tuple. -/
theorem okP_direct_inv (T : PSet.{4}) (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (A : Expr Nat)
    (x : PSet.{4}) (d : Nat)
    (hd : DirectRec fd.fref ar fd.params.length fd.indices.length d A)
    (h : okP P μ fd T σ ρ A x) :
    Equiv x pempty ∧ argsFitF P μ fd σ ρ A ∧
      tup ((familyIdx fd.params.length A).map (den (mkM P μ) σ ρ)) ∈ T := by
  simp only [okP, kindOf_directRec hd] at h
  exact h

include hB hpf hclsA hri hnoFn in
/-- The ⇐ walk: a `TelFitsP` read at a stage-carrying `T` re-reads as a
`TelFits` read at a late enough stage. -/
theorem telFits_iterSucc_of_telFitsP (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (hk : evalTotal σ fd.resLevel = 0)
    (T : PSet.{4}) (hT : ∀ z, z ∈ T → stageQ (P := P) (μ := μ) (fd := fd) σ ps z) :
    ∀ (Fs : List (Expr Nat)) (pre xs : List PSet.{4}),
    (∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn) →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs pre.length →
    TelFitsP P μ fd T σ Fs (push pre (push ps ρ0)) xs →
    ∃ N, TelFits (mkM P (tabIter P μ fd (N + 1))) σ Fs (push pre (push ps ρ0)) xs := by
  intro Fs
  induction Fs with
  | nil => intro pre xs _ _ h; cases xs with
    | nil => exact ⟨0, h⟩
    | cons x xs' => exact False.elim h
  | cons A Fs ih =>
      intro pre xs hnf hcl h
      obtain ⟨hdisj, hcl'⟩ := hcl
      have hnf' : ∀ p, p ∈ kindsOf fd.fref Fs → p ≠ PKind.fn := by
        intro p hp; exact hnf p (List.mem_cons_of_mem (kindOf fd.fref A) hp)
      cases xs with
      | nil => exact False.elim h
      | cons x xs' =>
          obtain ⟨hxP, hrestP⟩ := h
          have hcons : vcons x (push pre (push ps ρ0)) =
              push (pre ++ [x]) (push ps ρ0) :=
            (push_append pre [x] (push ps ρ0)).symm
          rw [hcons] at hrestP
          obtain ⟨N₂, hT2⟩ := ih (pre ++ [x]) xs' hnf' (by simp; exact hcl') hrestP
          obtain ⟨N₁, hN₂le, hhead⟩ : ∃ N₁, N₂ ≤ N₁ ∧ x ∈ Ed (mkM P (tabIter P μ fd (N₁ + 1)))
              (den (mkM P (tabIter P μ fd (N₁ + 1))) σ (push pre (push ps ρ0)) A) := by
            rcases hdisj with hfree | hd | hfn
            · have hx := okP_plain_inv (P := P) (μ := μ) (fd := fd) T σ
                (push pre (push ps ρ0)) A x hfree hxP
              refine ⟨N₂, Nat.le_refl _, ?_⟩
              show x ∈ Ed (mkM P (upd μ fd.fref (famIter P μ fd (N₂ + 1))))
                (den (mkM P (upd μ fd.fref (famIter P μ fd (N₂ + 1)))) σ
                  (push pre (push ps ρ0)) A)
              rw [den_off P μ fd.fref (famIter P μ fd (N₂ + 1)) σ _ hfree]
              rw [ed_mkM P (upd μ fd.fref (famIter P μ fd (N₂ + 1))) μ]
              exact hx
            · obtain ⟨hxp, hf, hm⟩ := okP_direct_inv (P := P) (μ := μ) (fd := fd) ar T σ
                (push pre (push ps ρ0)) A x pre.length hd hxP
              obtain ⟨idx, hAe, hidx, hfree⟩ := hd
              rw [hAe, familyIdx_directRec] at hm
              have hidxv : (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))).length =
                  fd.indices.length := (List.length_map _ _).trans hidx
              obtain ⟨m, is', heq, hlen', hφ⟩ := hT _ hm
              have hle : LEq is' (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) :=
                (tup_inj (hlen'.trans hidxv.symm) heq.symm)
              have hφv : ctorFitsStage P μ fd m σ ps
                  (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) :=
                ctorFitsStage_leq σ ps is'
                  (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) hle m hφ
              have hargs : ∀ e, e ∈ policyParameterLocals fd.params.length pre.length ++ idx →
                  occursConst fd.fref e = false := by
                intro e he
                rcases List.mem_append.mp he with hm | hm
                · exact paramLocals_free fd.fref fd.params.length pre.length e hm
                · exact hfree e hm
              have hl : (policyParameterLocals fd.params.length pre.length ++ idx).length =
                  (fd.params ++ fd.indices).length := by
                simp only [List.length_append, length_paramLocals, hidx]
              rw [hAe] at hf
              have hfit : RecFits P μ fd σ (push pre (push ps ρ0))
                  (policyParameterLocals fd.params.length pre.length ++ idx) :=
                (argsFitF_directRec P μ fd σ (push pre (push ps ρ0)) fd.fref (canonL ar) _).mp hf
              have hmap : (policyParameterLocals fd.params.length pre.length ++ idx).map
                  (den (mkM P μ) σ (push pre (push ps ρ0))) =
                  ps ++ idx.map (den (mkM P μ) σ (push pre (push ps ρ0))) := by
                rw [List.map_append]
                have he : push (ps ++ pre) ρ0 = push pre (push ps ρ0) :=
                  push_append ps pre ρ0
                congr 1
                rw [← hps]
                have hd := den_paramLocals (mkM P μ) σ ps pre ρ0
                rw [he] at hd
                exact hd
              have e1 := ed_rec_succ_fit P μ fd ar hB hpf m σ
                (push pre (push ps ρ0)) _ hargs hfit
              rw [hmap] at e1
              have e2 := famEnd_propStage (P := P) (μ := μ) σ ps
                (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) hidxv hk m
              rw [e2] at e1
              have hxt : x ∈ tv (ctorFitsStage P μ fd m σ ps
                  (idx.map (den (mkM P μ) σ (push pre (push ps ρ0))))) :=
                mem_tv.mpr ⟨hφv, hxp⟩
              have hx1 : x ∈ El (tyv (tv (ctorFitsStage P μ fd m σ ps
                  (idx.map (den (mkM P μ) σ (push pre (push ps ρ0))))))) :=
                mem_congr_right el_tyv.symm hxt
              have hx2 : x ∈ Ed (mkM P (tabIter P μ fd (m + 1)))
                  (den (mkM P (tabIter P μ fd (m + 1))) σ (push pre (push ps ρ0))
                    (foldApps (.const fd.fref (canonL ar))
                      (policyParameterLocals fd.params.length pre.length ++ idx))) :=
                mem_congr_right e1.symm hx1
              refine ⟨max m N₂, Nat.le_max_right _ _, ?_⟩
              rw [hAe]
              exact ed_iter_lift (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn
                (m + 1) (max m N₂ + 1) (by omega) σ (push pre (push ps ρ0))
                (policyParameterLocals fd.params.length pre.length ++ idx) hargs hl x hx2
            · exact absurd rfl (hnf _ (List.mem_map.mpr ⟨A, by simp, kindOf_fnRec hfn⟩))
          refine ⟨N₁, ⟨hhead, ?_⟩⟩
          rw [hcons]
          exact telFits_iter_lift (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hnoFn
            (N₂ + 1) (N₁ + 1) (by omega) σ ps hps Fs (pre ++ [x]) xs'
            hnf' (by simp; exact hcl') hT2

include hB hpf hclsA hri hres hnoFn in
/-- **⇐**: `DStarP` membership yields a stage truth (leastness of the union
of iterates, via `lfp_induction`). -/
theorem ctorFitsStage_of_dstarP (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (hk : evalTotal σ fd.resLevel = 0) (is : List PSet.{4})
    (hlen : is.length = fd.indices.length) :
    tup is ∈ DStarP P μ fd σ (push ps ρ0) →
    ∃ n, ctorFitsStage P μ fd n σ ps is := by
  have hstep : ∀ z, z ∈ PhiP P μ fd σ (push ps ρ0)
      (sep (stageQ (P := P) (μ := μ) (fd := fd) σ ps) (DStarP P μ fd σ (push ps ρ0))) →
      stageQ (P := P) (μ := μ) (fd := fd) σ ps z := by
    intro z hz
    obtain ⟨i, hp, hez⟩ := mem_sep.mp hz
    obtain ⟨j, c, xs, hc, htfP, ht⟩ := hp
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    have hT : ∀ z', z' ∈ sep (stageQ (P := P) (μ := μ) (fd := fd) σ ps)
        (DStarP P μ fd σ (push ps ρ0)) →
        stageQ (P := P) (μ := μ) (fd := fd) σ ps z' := by
      intro z' hz'
      obtain ⟨i₂, hp₂, he₂⟩ := mem_sep.mp hz'
      obtain ⟨n, is', heq2, hlen2, hφ2⟩ := hp₂
      exact ⟨n, is', he₂.symm.trans heq2, hlen2, hφ2⟩
    obtain ⟨N, htel⟩ := telFits_iterSucc_of_telFitsP (P := P) (μ := μ) (fd := fd) ar hB hpf
      hclsA hri hnoFn σ ps hps hk _ hT c.1
      [] xs (fun p hp2 => hnoFn c hcm p hp2) (hclsA c hcm) htfP
    have hdenm : (c.2.map (den (mkM P (tabIter P μ fd (N + 1))) σ (push xs (push ps ρ0)))) =
        c.2.map (den (mkM P μ) σ (push xs (push ps ρ0))) :=
      List.map_congr_left fun e he =>
        den_off P μ fd.fref (famIter P μ fd (N + 1)) σ _ (hri c hcm e he)
    exact ⟨N + 1, c.2.map (den (mkM P μ) σ (push xs (push ps ρ0))), hez.symm.trans ht,
      (List.length_map _ _).trans (hres c hcm), ⟨j, xs, c, hc, htel, by
        rw [hdenm]; exact LEq.refl _⟩⟩
  intro hm
  have hQ := lfp_induction (PhiP_ktop P μ fd σ (push ps ρ0))
    (stageQ (P := P) (μ := μ) (fd := fd) σ ps)
    (fun z z' he hq => by
      obtain ⟨n, is', heq, hlen', hφ⟩ := hq
      exact ⟨n, is', he.symm.trans heq, hlen', hφ⟩)
    hstep (tup is) hm
  obtain ⟨n, is', heq, hlen', hφ⟩ := hQ
  have hle : LEq is' is := tup_inj (hlen'.trans hlen.symm) heq.symm
  exact ⟨n, ctorFitsStage_leq σ ps is' is hle n hφ⟩

/-! ### §7 the entry-level twins -/

include hB hpf hclsA hri hres hnoFn in
/-- Pointwise at a split environment: the limit end is the `famEndP` truth. -/
theorem limEnd_famEndP (σ : Nat → Nat) (ps is : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (his : TelFits (mkM P μ) σ fd.indices (push ps ρ0) is)
    (hk : evalTotal σ fd.resLevel = 0) :
    Equiv (limEnd P μ fd σ (push (ps ++ is) ρ0))
      (famEndP P μ fd σ (push (ps ++ is) ρ0)) := by
  have hlen : is.length = fd.indices.length := TelFits.length his
  have e1 := limEnd_propStage (P := P) (μ := μ) (fd := fd) ar hB σ ps is hps hlen hk
  rw [push_append] at e1 ⊢
  rw [show famEndP P μ fd σ (push is (push ps ρ0)) =
      tyv (tv (tup is ∈ DStarP P μ fd σ (push ps ρ0))) from by
      unfold famEndP
      rw [← hlen, shiftρ_push, lastVals_push]]
  refine e1.trans (tyv_congr (tv_congr ⟨fun hex => ?_, fun hm => ?_⟩))
  · obtain ⟨n, hn⟩ := hex
    exact dstarP_of_ctorFitsStage (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hres hnoFn
      σ ps hps hk n is his hn
  · obtain ⟨n, hn⟩ := ctorFitsStage_of_dstarP (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA
      hri hres hnoFn σ ps hps hk is hlen hm
    exact ⟨n, hn⟩

include hB hpf hclsA hri hres hnoFn in
/-- The Prop twin of `famLim_famLfp`: at a Prop-read result level, the limit
of the iterates is `famLfpP`. -/
theorem famLim_famLfpP (vs : List Nat)
    (hk : evalTotal (σOf vs) fd.resLevel = 0) :
    Equiv (famLim P μ fd vs) (famLfpP P μ fd vs) := by
  show Equiv (piLam (mkM P μ) (σOf vs) (limEnd P μ fd (σOf vs)) ρ0 (famType fd))
    (piLam (mkM P μ) (σOf vs) (famEndP P μ fd (σOf vs)) ρ0 (famType fd))
  unfold famType
  exact piLam_congr_fits₂ (mkM P μ) (mkM P μ) rfl (σOf vs)
    (limEnd_resp P μ fd (σOf vs))
    (famEndP_envResp (P := P) (μ := μ) (fd := fd) (σOf vs))
    (.sort fd.resLevel) (fun A B e => Expr.noConfusion e)
    (fd.params ++ fd.indices) ρ0 (fun _ _ _ => rfl)
    (fun xs hxs => by
      obtain ⟨ps, is, hzs, hpsT, hisT⟩ :=
        TelFits_split fd.params fd.indices ρ0 xs hxs
      have hps : ps.length = fd.params.length := TelFits.length hpsT
      rw [hzs]
      exact limEnd_famEndP (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hres hnoFn
        (σOf vs) ps is hps hisT hk)

include hB hpf hclsA hri hres hnoFn in
/-- **The Prop twin of the bridge**: at a Prop-read result level, the limit
of the `F3` iterates is `famKT` (the `= 0` branch). -/
theorem famLim_famKT_prop (vs : List Nat)
    (hk : evalTotal (σOf vs) fd.resLevel = 0) :
    Equiv (famLim P μ fd vs) (famKT P μ fd vs) := by
  unfold famKT
  rw [if_pos hk]
  exact famLim_famLfpP (P := P) (μ := μ) (fd := fd) ar hB hpf hclsA hri hres hnoFn vs hk

end PropTwin

end PSet

end Rcic.F3

-- audit of record (replayed builds hide this: touch the file or read the log)
open Rcic.F3.PSet in
#print axioms Rcic.F3.PSet.famLim_famKT_prop
#print axioms Rcic.F3.PSet.famLim_famLfpP
#print axioms Rcic.F3.PSet.limEnd_famEndP
