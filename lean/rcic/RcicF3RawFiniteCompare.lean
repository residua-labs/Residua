import rcic.RcicF3RawFiniteFrame
import rcic.RcicF3RawFamilyView

/-!
# The normalized finite intersection is the existing finite limit

Induction on the existing finite iterates embeds each fitting application
into every admissible closed frame. Recursive fields use their complete
canonical universe vector and complete parameter/index key. Ordinary
dependent fields retain the same actual preceding values throughout.

The comparison is made at fitting family applications, as required by the
family abstraction. No assertion equates unused fibres, and no output
index fitting premise is added to constructor closure. closure_claim = 0.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Rcic.F3.PSet.RawFiniteCompare
open Rcic.Declarative PiIndex RawFamily RawFiniteFrame

private theorem telescope_refs (fd : FamData)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false) :
    RefsIn (fun r => r ≠ fd.fref) (fd.params ++ fd.indices) :=
  fun e he r hr => denRefs_ne_of_occurs e (hpf e he) r hr

/-- A nonempty complete application of any finite iterate satisfies the
literal family telescope. No universe bound or canonical-vector length is
required for this inversion. -/
theorem iterate_application_fits (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (n : Nat) (vs : List Nat) (ys : List PSet.{4})
    (hl : ys.length = (fd.params ++ fd.indices).length) (z : PSet.{4})
    (hz : z ∈ Ed (mkM P μ) (fapps (famIter P μ fd n vs) ys)) :
    TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys := by
  have hne : ¬ Equiv (fapps (famIter P μ fd n vs) ys) pempty := by
    intro he
    exact not_mem_pempty (mem_congr_right
      ((ed_congr (mkM P μ) he).trans (ed_pempty (mkM P μ))) hz)
  cases n with
  | zero =>
      exact fits_of_fapps_ne (mkM P μ) (σOf vs) (envResp_const (tyv pempty))
        (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 ys hl hne
  | succ n =>
      have hfit := fits_of_fapps_ne (mkM P (tabIter P μ fd n)) (σOf vs)
        (famEnd_resp (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd)
        (.sort fd.resLevel) (fd.params ++ fd.indices) ρ0 ys hl hne
      exact (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (famIter P μ fd n))
        (σOf vs) (fd.params ++ fd.indices) (telescope_refs fd hpf) ρ0 ys).mp hfit

/-- Every direct recursive field of an admissible frame is small at the
root stage, including empty applications outside the fitting telescope. -/
theorem recursive_frame_small (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
    (hB : FamBounded fd ar) (C : Frame) (hC : Admissible fd C)
    (σ : Nat → Nat) (ρ : Nat → PSet.{4}) (args : List (Expr Nat))
    (hargs : ∀ e ∈ args, occursConst fd.fref e = false)
    (hl : args.length = (fd.params ++ fd.indices).length) :
    Ed (mkM P (table P μ fd C))
      (den (mkM P (table P μ fd C)) σ ρ
        (foldApps (.const fd.fref (canonL ar)) args)) ∈
      W4 (evalTotal σ fd.resLevel) := by
  change Ed (mkM P (upd μ fd.fref (ofFrame P μ fd C)))
    (den (mkM P (upd μ fd.fref (ofFrame P μ fd C))) σ ρ
      (foldApps (.const fd.fref (canonL ar)) args)) ∈
    W4 (evalTotal σ fd.resLevel)
  rw [den_recApp P μ (ofFrame P μ fd C) σ ρ hargs]
  change Ed (mkM P μ)
    (fapps (ofFrame P μ fd C ((canonL ar).map (evalTotal σ)))
      (args.map (den (mkM P μ) σ ρ))) ∈ W4 (evalTotal σ fd.resLevel)
  let vs := (canonL ar).map (evalTotal σ)
  let ys := args.map (den (mkM P μ) σ ρ)
  have hys : ys.length = (fd.params ++ fd.indices).length :=
    (List.length_map _ _).trans hl
  have hlevel : evalTotal (σOf vs) fd.resLevel = evalTotal σ fd.resLevel :=
    evalTotal_agree (σOf_canon σ ar) fd.resLevel hB.res
  cases P.dec (TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys) with
  | isTrue hf =>
      have hm := (hC vs (key ys)).1
      rw [hlevel] at hm
      exact mem_congr_left (apply_ofFrame_ed P μ fd C hC vs ys hf).symm hm
  | isFalse hf =>
      have he := fapps_fam_nofit P μ fd (σOf vs)
        (endValue_resp C vs (fd.params.length + fd.indices.length)) ys hys hf
      exact mem_congr_left ((ed_congr (mkM P μ) he).trans
        (ed_pempty (mkM P μ))).symm (stageW4 P _).empty

/-- The existing constructor fibre closes into the exact quotient key.
Only the parameters must fit; the output indices need the literal length,
and need not fit their index types. -/
theorem closed_end_sub (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (C : Frame) (hc : Closed P μ fd C)
    (vs : List Nat) (ps is : List PSet.{4})
    (hp : TelFits (mkM P (table P μ fd C)) (σOf vs) fd.params ρ0 ps)
    (hi : is.length = fd.indices.length) :
    Sub (El (famEnd (mkM P (table P μ fd C)) W4 (σOf vs) fd
      (push (ps ++ is) ρ0))) (C vs (key (ps ++ is))) := by
  intro z hz
  unfold famEnd at hz
  rw [push_append, ← hi, shiftρ_push, lastVals_push] at hz
  by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [cond_pos h0] at hz
    obtain ⟨⟨j, xs, c, hj, hx, hresult⟩, hz0⟩ :=
      mem_tv.mp (mem_congr_right el_tyv hz)
    let k : Fin fd.ctors.length := ⟨j, (List.getElem?_eq_some_iff.mp hj).1⟩
    have hget : fd.ctors.get k = c := by
      rw [List.getElem?_eq_getElem k.isLt] at hj
      exact Option.some.inj hj
    apply hc vs (key (ps ++ is)) z
    refine ⟨k, ps, xs, hp, ?_, ?_, ?_, ?_⟩
    · rw [hget]; exact hx
    · rw [if_pos h0]; trivial
    · rw [hget]
      exact (key_eq_iff _ _).mpr (LEq_append (LEq.refl ps) hresult.symm)
    · rw [if_pos h0]; exact hz0
  · rw [cond_neg h0] at hz
    obtain ⟨j, xs, c, hj, hfit, hzv, hs⟩ :=
      mem_TypeFib.mp (mem_congr_right el_tyv hz)
    obtain ⟨c', hj', hx, hresult⟩ := hfit
    have hec : c' = c := Option.some.inj (hj'.symm.trans hj)
    subst c'
    let k : Fin fd.ctors.length := ⟨j, (List.getElem?_eq_some_iff.mp hj).1⟩
    have hget : fd.ctors.get k = c := by
      rw [List.getElem?_eq_getElem k.isLt] at hj
      exact Option.some.inj hj
    apply hc vs (key (ps ++ is)) z
    refine ⟨k, ps, xs, hp, ?_, ?_, ?_, ?_⟩
    · rw [hget]; exact hx
    · rw [if_neg h0, hget]; exact hs
    · rw [hget]
      exact (key_eq_iff _ _).mpr (LEq_append (LEq.refl ps) hresult.symm)
    · rw [if_neg h0]; exact hzv

private theorem iterate_fields (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
    (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (C : Frame) (hC : Admissible fd C) (n : Nat)
    (ih : ∀ vs ys, TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys →
      Sub (Ed (mkM P μ) (fapps (famIter P μ fd n vs) ys)) (C vs (key ys)))
    (σ : Nat → Nat) :
    FamLE (mkM P (tabIter P μ fd n)) (mkM P (table P μ fd C))
      (W4 (evalTotal σ fd.resLevel)) σ fd.ctors := by
  apply famLE_upd P μ fd ar hcls hri (famIter P μ fd n) (ofFrame P μ fd C) σ
  · intro ρ args hargs hl z hz
    rw [den_recApp P μ (famIter P μ fd n) σ ρ hargs] at hz
    rw [den_recApp P μ (ofFrame P μ fd C) σ ρ hargs]
    let vs := (canonL ar).map (evalTotal σ)
    let ys := args.map (den (mkM P μ) σ ρ)
    have hf : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys :=
      iterate_application_fits P μ fd hpf n vs ys
        ((List.length_map _ _).trans hl) z hz
    exact mem_congr_right (apply_ofFrame_ed P μ fd C hC vs ys hf).symm
      (ih vs ys hf z hz)
  · intro ρ args hargs hl
    exact recursive_frame_small P μ fd ar hB C hC σ ρ args hargs hl

/-- Every finite iterate is below every admissible closed frame, jointly
over all universe vectors and complete fitting argument tuples. -/
theorem iterate_below (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C) :
    ∀ n vs ys, TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys →
      Sub (Ed (mkM P μ) (fapps (famIter P μ fd n vs) ys)) (C vs (key ys)) := by
  intro n
  induction n with
  | zero =>
      intro vs ys hf z hz
      have hb := fapps_fam_fit P μ fd (σOf vs) (envResp_const (tyv pempty)) ys hf
      exact (not_mem_pempty (mem_congr_right
        ((ed_congr (mkM P μ) hb).trans (ed_tyv_empty (mkM P μ))) hz)).elim
  | succ n ih =>
      intro vs ys hf z hz
      have hT := (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (famIter P μ fd n))
        (σOf vs) (fd.params ++ fd.indices) (telescope_refs fd hpf) ρ0 ys).mpr hf
      have hb := fapps_fam_fit P (tabIter P μ fd n) fd (σOf vs)
        (famEnd_resp (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd) ys hT
      have hzEnd : z ∈ El (famEnd (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd
          (push ys ρ0)) :=
        mem_congr_right ((ed_congr (mkM P μ) hb).trans
          (ed_famEnd (mkM P (tabIter P μ fd n)) (mkM P μ) rfl
            (σOf vs) fd (push ys ρ0))) hz
      have hzC := el_famEnd_mono P
        (iterate_fields P μ fd ar hB hpf hcls hri C hC n ih (σOf vs))
        (push ys ρ0) hzEnd
      obtain ⟨ps, is, rfl, hps, his⟩ := TelFits_split fd.params fd.indices ρ0 ys hf
      have hpC := (TelFits_agreeOn P
        (agreeOn_upd_off μ fd.fref (ofFrame P μ fd C)) (σOf vs) fd.params
        (fun A hA r hr => telescope_refs fd hpf A
          (List.mem_append_left _ hA) r hr) ρ0 ps).mpr hps
      exact closed_end_sub P μ fd C hc vs ps is hpC his.length z hzC

theorem fibre_below (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (C : Frame) (hC : Admissible fd C) (hc : Closed P μ fd C)
    (vs : List Nat) (ys : List PSet.{4})
    (hf : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys) :
    Sub (fibre P μ fd (σOf vs) (push ys ρ0)) (C vs (key ys)) := by
  intro z hz
  obtain ⟨n, hn⟩ := mem_iUnionN.mp hz
  have hT := (TelFits_agreeOn P (agreeOn_upd_off μ fd.fref (famIter P μ fd n))
    (σOf vs) (fd.params ++ fd.indices) (telescope_refs fd hpf) ρ0 ys).mpr hf
  have hb := fapps_fam_fit P (tabIter P μ fd n) fd (σOf vs)
    (famEnd_resp (mkM P (tabIter P μ fd n)) W4 (σOf vs) fd) ys hT
  have happ : z ∈ Ed (mkM P μ) (fapps (famIter P μ fd (n + 1) vs) ys) :=
    mem_congr_right ((ed_congr (mkM P μ) hb).trans
      (ed_famEnd (mkM P (tabIter P μ fd n)) (mkM P μ) rfl
        (σOf vs) fd (push ys ρ0))).symm hn
  exact iterate_below P μ fd ar hB hpf hcls hri C hC hc (n + 1) vs ys hf z happ

/-- Equality at complete fitting keys. Unused fibre values are deliberately
absent from the statement; constructor closure itself had no index-fit test. -/
theorem raw_fibre (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (hcount : ∀ c ∈ fd.ctors, c.2.length = fd.indices.length)
    (vs : List Nat) (ys : List PSet.{4})
    (hf : TelFits (mkM P μ) (σOf vs) (fd.params ++ fd.indices) ρ0 ys) :
    Equiv (frame P μ fd vs (key ys)) (fibre P μ fd (σOf vs) (push ys ρ0)) := by
  apply ext
  intro z
  constructor
  · intro hz
    exact mem_congr_right (candidate_key P μ fd vs ys)
      (frame_least P μ fd (candidate P μ fd) (candidate_admissible P μ fd)
        (candidate_closed P μ fd ar hB hpf hcls hri hcount) vs (key ys) z hz)
  · intro hz
    have hall : InAll P μ fd vs (key ys) z := by
      intro C hC hc
      exact fibre_below P μ fd ar hB hpf hcls hri C hC hc vs ys hf z hz
    by_cases h0 : evalTotal (σOf vs) fd.resLevel = 0
    · have he := fibre_prop P μ fd (σOf vs) h0 (push ys ρ0) z hz
      unfold frame
      rw [if_pos h0]
      exact mem_tv.mpr ⟨fun C hC hc => mem_congr_left he (hall C hC hc), he⟩
    · obtain ⟨j, hj⟩ := (stageW4 P _).trans
        (fibre_mem P μ fd (σOf vs) (push ys ρ0)) hz
      unfold frame
      rw [if_neg h0]
      exact mem_sep.mpr ⟨j, (inAll_resp P μ fd vs (key ys) hj.symm).mp hall, hj⟩

/-- The literal raw intersection role at the normalized finite signature
is the existing finite limit at every full universe vector. -/
theorem role_value (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (hB : FamBounded fd ar)
    (hpf : ∀ e ∈ fd.params ++ fd.indices, occursConst fd.fref e = false)
    (hcls : ∀ c ∈ fd.ctors, ∀ A ∈ c.1,
      occursConst fd.fref A = false ∨ RecApp fd ar A)
    (hri : ∀ c ∈ fd.ctors, ∀ e ∈ c.2, occursConst fd.fref e = false)
    (hcount : ∀ c ∈ fd.ctors, c.2.length = fd.indices.length)
    (vs : List Nat) : Equiv (role P μ fd vs) (famLim P μ fd vs) := by
  unfold role ofFrame famLim famType
  apply piLam_congr_fits (mkM P μ) (σOf vs) (.sort fd.resLevel)
    (fun _ _ h => Expr.noConfusion h) (fd.params ++ fd.indices) ρ0
  intro ys hf
  change Equiv (tyv (frame P μ fd vs
    (key (lastVals (fd.params.length + fd.indices.length) (push ys ρ0)))))
    (tyv (fibre P μ fd (σOf vs) (push ys ρ0)))
  have hl : fd.params.length + fd.indices.length = ys.length := by
    rw [hf.length, List.length_append]
  rw [hl, lastVals_push]
  exact tyv_congr (raw_fibre P μ fd ar hB hpf hcls hri hcount vs ys hf)

end Rcic.F3.PSet.RawFiniteCompare
