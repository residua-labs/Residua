import rcic.RcicF3KTWProp

/-!
# F3 S7 KT-2d-2b: Prop-instance dictionary and fixed point.

`mem_field_P` reads a constructor field under `MP` as the `okP` condition;
`telFits_iff_TelFitsP` lifts it along a field telescope; `PropFib_famLfpP`
identifies the `PropFib` proposition with membership in `DStarP`;
`famVal_famLfpP` is the fixed-point equation at `kk = 0`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

namespace PSet

open Rcic.Declarative

universe T

/-- `Ed` of a `piVal` in its `PiProp` branch is the `tv` of the proof
condition. -/
theorem ed_piVal_of_prop (M : Interp.{T}) {A : PSet.{T}} {B : PSet.{T} → PSet.{T}}
    (h : PiProp M A B) :
    Equiv (Ed M (piVal M A B)) (tv (∀ x, x ∈ Ed M A → pempty ∈ Ed M (B x))) := by
  show Equiv (Ed M (tyv (cond M.dec _ _ _))) _
  rw [cond_pos h]
  exact ed_tyv_of_dich M (dich_tv _)

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hclsA : ∀ c, c ∈ fd.ctors →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
  (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)

include hB hpf

/-- L0P: a recursive occurrence at depth `pre.length` denotes `tv` of the
fit-and-membership condition under `famLfpP`. -/
theorem ed_recOccP (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (idx : List (Expr Nat)) (hidx : idx.length = fd.indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst fd.fref e = false) :
    Equiv (Ed (mkM P (upd μ fd.fref (famLfpP P μ fd)))
        (den (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ (push pre (push ps ρ0))
          (foldApps (.const fd.fref (canonL ar))
            (policyParameterLocals fd.params.length pre.length ++ idx))))
      (tv (argsFitF P μ fd σ (push pre (push ps ρ0))
          (foldApps (.const fd.fref (canonL ar))
            (policyParameterLocals fd.params.length pre.length ++ idx)) ∧
        tup (idx.map (den (mkM P μ) σ (push pre (push ps ρ0)))) ∈
          DStarP P μ fd σ (push ps ρ0))) := by
  let ρ' := push pre (push ps ρ0)
  let args := policyParameterLocals fd.params.length pre.length ++ idx
  let A' := foldApps (.const fd.fref (canonL ar)) args
  have hargs : ∀ e, e ∈ args → occursConst fd.fref e = false := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact paramLocals_free fd.fref fd.params.length pre.length e h
    · exact hfree e h
  have hmap : args.map (den (mkM P μ) σ ρ') =
      ps ++ idx.map (den (mkM P μ) σ ρ') := by
    rw [List.map_append]
    have he : push (ps ++ pre) ρ0 = ρ' := push_append ps pre ρ0
    congr 1
    rw [← hps]
    have hd := den_paramLocals (mkM P μ) σ ps pre ρ0
    rw [he] at hd
    exact hd
  cases P.dec (argsFitF P μ fd σ ρ' A') with
  | isTrue hfit =>
      have htf : TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
          (args.map (den (mkM P μ) σ ρ')) :=
        (argsFitF_directRec P μ fd σ ρ' fd.fref (canonL ar) args).mp hfit
      have e1 := ed_recApp_fit P μ fd ar (hpi_of fd ar hB) hpf
        (famLfpP P μ fd) μ (famEndP P μ fd)
        (fun _ => rfl) (fun _ _ _ => rfl)
        (fun σ' => famEndP_envResp P μ fd σ')
        (fun σ' σ'' hσ ρ => famEndP_levels P μ fd ar hB hσ ρ)
        σ ρ' args hargs htf
      rw [hmap] at e1
      -- e1 : Ed MP (…) ≈ Ed (mkM P μ) (famEndP σ (push (ps ++ idxv) ρ0))
      have hidxv : (idx.map (den (mkM P μ) σ ρ')).length = fd.indices.length :=
        (List.length_map _ _).trans hidx
      have e2 : Equiv (Ed (mkM P μ) (famEndP P μ fd σ (push (ps ++ idx.map (den (mkM P μ) σ ρ')) ρ0)))
          (tv (tup (idx.map (den (mkM P μ) σ ρ')) ∈ DStarP P μ fd σ (push ps ρ0))) := by
        show Equiv (Ed (mkM P μ) (tyv (tv _))) _
        refine (ed_tyv_of_dich (mkM P μ) (dich_tv _)).trans (tv_congr ?_)
        rw [push_append, ← hidxv, shiftρ_push, lastVals_push]
      exact e1.trans (e2.trans (tv_congr
        ⟨fun hm => ⟨hfit, hm⟩, fun hm => hm.2⟩))
  | isFalse hnf =>
      have hnf' : ¬ TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
          (args.map (den (mkM P μ) σ ρ')) :=
        fun h => hnf ((argsFitF_directRec P μ fd σ ρ' fd.fref (canonL ar) args).mpr h)
      have hl : args.length = (fd.params ++ fd.indices).length := by
        show (policyParameterLocals fd.params.length pre.length ++ idx).length = _
        rw [List.length_append, length_paramLocals, hidx, List.length_append]
      have e1 := ed_recApp_nofit P μ fd ar (hpi_of fd ar hB) hpf
        (famLfpP P μ fd) μ (famEndP P μ fd)
        (fun _ => rfl) (fun _ _ _ => rfl)
        (fun σ' => famEndP_envResp P μ fd σ')
        σ ρ' args hargs hl hnf'
      refine e1.trans ?_
      apply ext; intro z; constructor
      · intro hz; exact absurd hz not_mem_pempty
      · intro hz; exact absurd ((mem_tv.mp hz).1.1) hnf

/-- A family-free field's `Ed`-membership under `MP` is the `okP` condition. -/
theorem mem_field_P_plain (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length) {A : Expr Nat}
    (hA : occursConst fd.fref A = false) (x : PSet.{4}) :
    x ∈ Ed (mkM P (upd μ fd.fref (famLfpP P μ fd)))
        (den (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ (push pre (push ps ρ0)) A) ↔
      okP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ (push pre (push ps ρ0)) A x := by
  rw [den_off P μ fd.fref (famLfpP P μ fd) σ (push pre (push ps ρ0)) hA]
  show x ∈ Ed (mkM P μ) (den (mkM P μ) σ (push pre (push ps ρ0)) A) ↔ _
  simp only [okP]
  cases hk : kindOf fd.fref A with
  | plain => exact Iff.rfl
  | direct => exact absurd hk (by rw [kindOf_free hA]; exact fun h => PKind.noConfusion h)
  | fn => exact absurd hk (by rw [kindOf_free hA]; exact fun h => PKind.noConfusion h)

/-- A `DirectRec` field's `Ed`-membership under `MP` is the `okP` condition. -/
theorem mem_field_P_direct (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length) {A : Expr Nat}
    (hA : DirectRec fd.fref ar fd.params.length fd.indices.length pre.length A)
    (x : PSet.{4}) :
    x ∈ Ed (mkM P (upd μ fd.fref (famLfpP P μ fd)))
        (den (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ (push pre (push ps ρ0)) A) ↔
      okP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ (push pre (push ps ρ0)) A x := by
  obtain ⟨idx, hAe, hidx, hfree⟩ := hA
  rw [hAe]
  have e1 := ed_recOccP P μ fd ar hB hpf σ ps pre hps idx hidx hfree
  simp only [okP]
  cases hk : kindOf fd.fref (foldApps (.const fd.fref (canonL ar))
      (policyParameterLocals fd.params.length pre.length ++ idx)) with
  | plain => exact absurd hk (by
      have hkd := kindOf_directRec ⟨idx, hAe, hidx, hfree⟩
      rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)
  | direct =>
      rw [familyIdx_directRec]
      exact ⟨fun hx => let ⟨hφ, hxp⟩ := mem_tv.mp (mem_congr_right e1 hx)
          ⟨hxp, hφ.1, hφ.2⟩,
        fun ⟨hxp, hf, hm⟩ => mem_congr_right e1.symm
          (mem_tv.mpr ⟨⟨hf, hm⟩, hxp⟩)⟩
  | fn => exact absurd hk (by
      have hkd := kindOf_directRec ⟨idx, hAe, hidx, hfree⟩
      rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)

/-- A `FnRec` field's `Ed`-membership under `MP` is the `okP` condition. -/
theorem mem_field_P_fn (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length) {A : Expr Nat}
    (hA : FnRec fd.fref ar fd.params.length fd.indices.length pre.length A)
    (x : PSet.{4}) :
    x ∈ Ed (mkM P (upd μ fd.fref (famLfpP P μ fd)))
        (den (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ (push pre (push ps ρ0)) A) ↔
      okP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ (push pre (push ps ρ0)) A x := by
  obtain ⟨D', idx, hAe, hidx, hD', hfree⟩ := hA
  rw [hAe]
  let ρ' := push pre (push ps ρ0)
  let ρp := push ps ρ0
  let MP := mkM P (upd μ fd.fref (famLfpP P μ fd))
  let B := foldApps (.const fd.fref (canonL ar))
    (policyParameterLocals fd.params.length (pre.length + 1) ++ idx)
  have hvey : ∀ y : PSet.{4}, vcons y ρ' = push (pre ++ [y]) ρp := by
    intro y; exact (push_append pre [y] (push ps ρ0)).symm
  have hlen : ∀ y : PSet.{4}, (pre ++ [y]).length = pre.length + 1 :=
    fun y => (List.length_append _ _).trans (by simp)
  have hfib : ∀ y : PSet.{4},
      Equiv (Ed MP (den MP σ (vcons y ρ') B))
        (tv (argsFitF P μ fd σ (vcons y ρ') B ∧
          tup (idx.map (den (mkM P μ) σ (vcons y ρ'))) ∈ DStarP P μ fd σ ρp)) := by
    intro y
    have e1 := ed_recOccP P μ fd ar hB hpf σ ps (pre ++ [y]) hps idx hidx hfree
    rw [hlen y] at e1
    rw [hvey y]
    exact e1
  have hPi : PiProp MP (den MP σ ρ' D') (fun y => den MP σ (vcons y ρ') B) :=
    fun a ha y hy => (mem_tv.mp (mem_congr_right (hfib a) hy)).2
  have e1 := ed_piVal_of_prop MP hPi
  simp only [okP]
  cases hk : kindOf fd.fref (.pi D' B) with
  | plain => exact absurd hk (by
      have hkd := kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩
      rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)
  | direct => exact absurd hk (by
      have hkd := kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩
      rw [hAe] at hkd; rw [hkd]; exact fun h => PKind.noConfusion h)
  | fn =>
      have hfi : familyIdx fd.params.length (piCod (.pi D' B)) = idx :=
        familyIdx_directRec _ _ _ _ _
      rw [hfi]
      have hdenD' : den MP σ ρ' D' = den (mkM P μ) σ ρ' D' :=
        den_off P μ fd.fref (famLfpP P μ fd) σ ρ' hD'
      refine ⟨fun hx => ?_, fun ⟨hxp, hf⟩ => ?_⟩
      · have ⟨hφ, hxp⟩ := mem_tv.mp (mem_congr_right e1 hx)
        refine ⟨hxp, fun y hy => ?_⟩
        have hy' : pempty ∈ Ed MP (den MP σ (vcons y ρ') B) := hφ y
          (by rw [hdenD']; exact hy)
        exact (mem_tv.mp (mem_congr_right (hfib y) hy')).1
      · have hφ : ∀ y, y ∈ Ed MP (den MP σ ρ' D') → pempty ∈ Ed MP (den MP σ (vcons y ρ') B) := by
          intro y hy
          have hy' : y ∈ Ed (mkM P μ) (den (mkM P μ) σ ρ' D') := by
            rw [hdenD'] at hy
            have hed : Ed MP (den (mkM P μ) σ ρ' D') =
                Ed (mkM P μ) (den (mkM P μ) σ ρ' D') :=
              Ed_dec_eq P (upd μ fd.fref (famLfpP P μ fd)) μ _
            rw [hed] at hy; exact hy
          have ⟨hfy, hmy⟩ := hf y hy'
          exact mem_congr_right (hfib y).symm (mem_tv.mpr ⟨⟨hfy, hmy⟩, Equiv.rfl⟩)
        exact mem_congr_right e1.symm (mem_tv.mpr ⟨hφ, hxp⟩)

/-- `TelFits` under `MP` is `TelFitsP` at `DStarP`, along a class-A
telescope. -/
theorem telFits_iff_TelFitsP_gen (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) :
    ∀ (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest pre.length →
      (TelFits (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ rest
          (push pre (push ps ρ0)) xs ↔
        TelFitsP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ rest
          (push pre (push ps ρ0)) xs) := by
  intro rest
  induction rest with
  | nil =>
      intro pre xs hcls
      cases xs with
      | nil => exact ⟨fun _ => trivial, fun _ => trivial⟩
      | cons x xs => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
  | cons A rest' ih =>
      intro pre xs hcls
      obtain ⟨hdisj, hcls'⟩ := hcls
      cases xs with
      | nil => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
      | cons x xs' =>
          have hlen : (pre ++ [x]).length = pre.length + 1 := by simp
          have hcons : vcons x (push pre (push ps ρ0)) =
              push (pre ++ [x]) (push ps ρ0) :=
            (push_append pre [x] (push ps ρ0)).symm
          have hih := ih (pre ++ [x]) xs' (hlen ▸ hcls')
          rw [← hcons] at hih
          rcases hdisj with h | h | h
          · show (_ ∧ _) ↔ (okP P μ fd _ σ _ A x ∧ _)
            exact and_congr (mem_field_P_plain P μ fd ar hB hpf σ ps pre hps h x) hih
          · show (_ ∧ _) ↔ (okP P μ fd _ σ _ A x ∧ _)
            exact and_congr (mem_field_P_direct P μ fd ar hB hpf σ ps pre hps h x) hih
          · show (_ ∧ _) ↔ (okP P μ fd _ σ _ A x ∧ _)
            exact and_congr (mem_field_P_fn P μ fd ar hB hpf σ ps pre hps h x) hih

/-- `TelFits` under `MP` at a class-A constructor telescope is `TelFitsP`. -/
theorem telFits_iff_TelFitsP (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    {Fs : List (Expr Nat)}
    (hcls : FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs 0)
    (xs : List PSet.{4}) :
    TelFits (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ Fs (push ps ρ0) xs ↔
      TelFitsP P μ fd (DStarP P μ fd σ (push ps ρ0)) σ Fs (push ps ρ0) xs := by
  exact telFits_iff_TelFitsP_gen P μ fd ar hB hpf σ ps hps Fs [] xs hcls

include hclsA hri hres

/-- The `PropFib` proposition under `MP` at `famLfpP` is membership in
`DStarP`. -/
theorem PropFib_famLfpP (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) (is : List PSet.{4})
    (his : TelFits (mkM P μ) σ fd.indices (push ps ρ0) is) :
    (∃ j xs, CtorFits (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ fd.ctors
        (push ps ρ0) is j xs) ↔
      tup is ∈ DStarP P μ fd σ (push ps ρ0) := by
  let MP := mkM P (upd μ fd.fref (famLfpP P μ fd))
  let ρp := push ps ρ0
  constructor
  · rintro ⟨j, xs, c, hc, htf, hle⟩
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    have htfP : TelFitsP P μ fd (DStarP P μ fd σ ρp) σ c.1 ρp xs :=
      (telFits_iff_TelFitsP P μ fd ar hB hpf σ ps hps
        (hclsA c hcm) xs).mp htf
    have hresμ : c.2.map (den (mkM P μ) σ (push xs ρp)) =
        c.2.map (den MP σ (push xs ρp)) :=
      List.map_congr_left fun e he =>
        (den_off P μ fd.fref (famLfpP P μ fd) σ (push xs ρp)
          (hri c hcm e he)).symm
    have hUP : tup is ∈ UP P μ fd σ ρp :=
      ((mem_FitSetU_iff (mkM P μ) σ fd.indices ρp).mpr ⟨is, Equiv.rfl, his⟩)
    obtain ⟨i, hi⟩ := hUP
    have hmem : tup is ∈ PhiP P μ fd σ ρp (DStarP P μ fd σ ρp) :=
      mem_sep.mpr ⟨i, ⟨j, c, xs, hc, htfP,
        hi.trans ((tup_congr (hresμ ▸ hle)).symm)⟩, hi⟩
    exact (DStarP_isLfp P μ fd σ ρp).1 _ hmem
  · intro hm
    have hmem : tup is ∈ PhiP P μ fd σ ρp (DStarP P μ fd σ ρp) :=
      (DStarP_isLfp P μ fd σ ρp).2.1 _ hm
    obtain ⟨i, hp, he⟩ := mem_sep.mp
      (show tup is ∈ sep _ (UP P μ fd σ ρp) from hmem)
    obtain ⟨j, c, xs, hc, htf, ht⟩ := hp
    have hcm : c ∈ fd.ctors := List.getElem?_mem hc
    have hresμ : c.2.map (den MP σ (push xs ρp)) =
        c.2.map (den (mkM P μ) σ (push xs ρp)) :=
      List.map_congr_left fun e he =>
        den_off P μ fd.fref (famLfpP P μ fd) σ (push xs ρp)
          (hri c hcm e he)
    exact ⟨j, xs, ⟨c, hc,
      (telFits_iff_TelFitsP P μ fd ar hB hpf σ ps hps
        (hclsA c hcm) xs).mpr htf,
      hresμ ▸ tup_inj ((List.length_map _ _).trans
        ((hres c hcm).trans (TelFits.length his).symm))
        (ht.symm.trans he)⟩⟩

/-- The family's `famVal` under `MP` at `kk = 0` is `famLfpP`. -/
theorem famVal_famLfpP (vs : List Nat)
    (hk0 : evalTotal (σOf vs) fd.resLevel = 0) :
    Equiv (famVal (mkM P (upd μ fd.fref (famLfpP P μ fd))) W4 (σOf vs) fd)
      (famLfpP P μ fd vs) := by
  let σ := σOf vs
  let MP := mkM P (upd μ fd.fref (famLfpP P μ fd))
  show Equiv (piLam MP σ (famEnd MP W4 σ fd) ρ0 (famType fd))
    (piLam (mkM P μ) σ (famEndP P μ fd σ) ρ0 (famType fd))
  show Equiv (piLam MP σ (famEnd MP W4 σ fd) ρ0
      (policyPi (fd.params ++ fd.indices) (.sort fd.resLevel)))
    (piLam (mkM P μ) σ (famEndP P μ fd σ) ρ0
      (policyPi (fd.params ++ fd.indices) (.sort fd.resLevel)))
  refine piLam_congr_fits₂ MP (mkM P μ) rfl σ
    (famEnd_resp MP W4 σ fd) (famEndP_envResp P μ fd σ)
    (.sort fd.resLevel) (fun A B h => Expr.noConfusion h)
    (fd.params ++ fd.indices) ρ0
    (fun ρ' A hA => den_off P μ fd.fref (famLfpP P μ fd) σ ρ' (hpf A hA))
    (fun xs hfits => ?_)
  obtain ⟨ps, is, hzs, hpsT, hisT⟩ := TelFits_split _ _ _ _ hfits
  rw [hzs]
  have hps : ps.length = fd.params.length := TelFits.length hpsT
  have his : is.length = fd.indices.length := TelFits.length hisT
  rw [push_append]
  show Equiv (famEnd MP W4 σ fd (push is (push ps ρ0)))
    (famEndP P μ fd σ (push is (push ps ρ0)))
  rw [show famEnd MP W4 σ fd (push is (push ps ρ0)) =
      tyv (tv (∃ j xs, CtorFits MP σ fd.ctors
        (shiftρ fd.indices.length (push is (push ps ρ0)))
        (lastVals fd.indices.length (push is (push ps ρ0))) j xs)) from by
        show famEnd MP W4 σ fd _ = _
        unfold famEnd
        rw [cond_pos hk0]
        rfl]
  rw [← his, shiftρ_push, lastVals_push]
  rw [show famEndP P μ fd σ (push is (push ps ρ0)) =
      tyv (tv (tup is ∈ DStarP P μ fd σ (push ps ρ0))) from by
        unfold famEndP
        rw [← his, shiftρ_push, lastVals_push]]
  show Equiv (tyv (tv (∃ j xs, CtorFits MP σ fd.ctors (push ps ρ0) is j xs)))
    (tyv (tv (tup is ∈ DStarP P μ fd σ (push ps ρ0))))
  exact tyv_congr (tv_congr
    (PropFib_famLfpP P μ fd ar hB hpf hclsA hri hres σ ps hps is
      (by show TelFits (mkM P μ) σ fd.indices (push ps ρ0) is
          have hden : ∀ e ∈ fd.indices, ∀ ρ,
              den MP σ ρ e = den (mkM P μ) σ ρ e :=
            fun e he ρ => den_off P μ fd.fref
              (famLfpP P μ fd) σ ρ (hpf e (List.mem_append.mpr (Or.inr he)))
          exact (TelFits_den_iff P (upd μ fd.fref (famLfpP P μ fd)) μ σ fd.indices hden (push ps ρ0) is).mp hisT)))

end

end PSet

end Rcic.F3
