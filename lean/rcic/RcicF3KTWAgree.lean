/- KT-2e: the combined family entry reads the table only at the family's
references (`famKT_agreeOn`), the `tablesOn` analogue of `famLim_agreeOn`. -/

import rcic.RcicF3KTWFamKT

universe T

namespace Rcic.F3.PSet

open Rcic.Declarative
open Rcic.Model.PS (denRefs)

/-- Every reference of a `foldApps` argument or head is a reference of the
whole. -/
theorem refs_foldApps_ag {r : Nat} : (g : Expr Nat) → (as : List (Expr Nat)) →
    (r ∈ denRefs g ∨ ∃ a, a ∈ as ∧ r ∈ denRefs a) →
    r ∈ denRefs (foldApps g as)
  | _, [], h => by
      rcases h with h | ⟨a, ha, _⟩
      · exact h
      · exact absurd ha (List.not_mem_nil _)
  | g, a :: as, h => by
      refine refs_foldApps_ag (.app g a) as ?_
      rcases h with h | ⟨a', ha', hr⟩
      · exact Or.inl (List.mem_append_left _ h)
      · rcases List.mem_cons.mp ha' with rfl | ha'
        · exact Or.inl (List.mem_append_right _ hr)
        · exact Or.inr ⟨a', ha', hr⟩

/-- The references of a family-free expression avoid `f`. -/
theorem refs_of_free {f : Nat} {e : Expr Nat} (hfree : occursConst f e = false)
    {S : Nat → Prop} (hb : ∀ r, r ∈ denRefs e → S r ∨ r = f) :
    ∀ r, r ∈ denRefs e → S r :=
  fun r hr => (hb r hr).elim id fun hf =>
    absurd hf (denRefs_ne_of_occurs e hfree r hr)

/-- `policyParameterLocals` are bound variables; they carry no references. -/
theorem refs_paramLocals {S : Nat → Prop} (np d : Nat) :
    RefsIn S (policyParameterLocals np d) :=
  fun e he r hr => absurd rfl
    (denRefs_ne_of_occurs e (paramLocals_free r np d e he) r hr)

/-- `RefsIn` distributes over append. -/
theorem RefsIn_append {S : Nat → Prop} {xs ys : List (Expr Nat)}
    (hx : RefsIn S xs) (hy : RefsIn S ys) : RefsIn S (xs ++ ys) :=
  fun e he => (List.mem_append.mp he).elim (hx e) (hy e)

/-- Every reference of a `foldApps` argument is a reference of the whole. -/
theorem refs_foldApps_arg {f : Nat} {ls : List Level} {args : List (Expr Nat)}
    {e : Expr Nat} (he : e ∈ args) {r : Nat} (hr : r ∈ denRefs e) :
    r ∈ denRefs (foldApps (.const f ls) args) :=
  refs_foldApps_ag (.const f ls) args (Or.inr ⟨e, he, hr⟩)

/-- `RefsIn` for the argument list of a direct recursive occurrence. -/
theorem refs_directRec_args {f ar np nq d : Nat} {A : Expr Nat}
    (h : DirectRec f ar np nq d A) {S : Nat → Prop}
    (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = f) :
    RefsIn S (appsSpine A).2 := by
  obtain ⟨idx, hAe, _, hfree⟩ := h
  rw [hAe]
  have hsp : (appsSpine (foldApps (.const f (canonL ar))
        (policyParameterLocals np d ++ idx))).2 =
      policyParameterLocals np d ++ idx := by
    rw [appsSpine_foldApps]
    rfl
  rw [hsp]
  exact RefsIn_append (refs_paramLocals np d) fun e he r hr =>
    refs_of_free (hfree e he) (fun r' hr' =>
      hbA r' (hAe ▸ refs_foldApps_arg (List.mem_append_right _ he) hr')) r hr

/-- `RefsIn` for the family index list of a direct recursive occurrence. -/
theorem refs_directRec_familyIdx {f ar np nq d : Nat} {A : Expr Nat}
    (h : DirectRec f ar np nq d A) {S : Nat → Prop}
    (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = f) :
    RefsIn S (familyIdx np A) := by
  obtain ⟨idx, hAe, _, hfree⟩ := h
  rw [hAe, familyIdx_directRec]
  exact fun e he r hr => refs_of_free (hfree e he) (fun r' hr' =>
    hbA r' (hAe ▸ refs_foldApps_arg (List.mem_append_right _ he) hr')) r hr

/-- `RefsIn` for the argument list of an `fn` recursive occurrence's
codomain. -/
theorem refs_fnRec_args {f ar np nq d : Nat} {A : Expr Nat}
    (h : FnRec f ar np nq d A) {S : Nat → Prop}
    (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = f) :
    RefsIn S (appsSpine (piCod A)).2 := by
  obtain ⟨D', idx, hAe, _, _, hfree⟩ := h
  rw [hAe]
  have hsp : (appsSpine (piCod (.pi D' (foldApps (.const f (canonL ar))
        (policyParameterLocals np (d + 1) ++ idx))))).2 =
      policyParameterLocals np (d + 1) ++ idx := by
    show (appsSpine (foldApps (.const f (canonL ar))
      (policyParameterLocals np (d + 1) ++ idx))).2 = _
    rw [appsSpine_foldApps]
    rfl
  rw [hsp]
  exact RefsIn_append (refs_paramLocals np (d + 1)) fun e he r hr =>
    (refs_of_free (hfree e he) (fun r' hr' =>
      hbA r' (hAe ▸ List.mem_append_right _
        (refs_foldApps_arg (List.mem_append_right _ he) hr')))) r hr

/-- `RefsIn` for the family index list of an `fn` recursive occurrence's
codomain. -/
theorem refs_fnRec_familyIdx {f ar np nq d : Nat} {A : Expr Nat}
    (h : FnRec f ar np nq d A) {S : Nat → Prop}
    (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = f) :
    RefsIn S (familyIdx np (piCod A)) := by
  obtain ⟨D', idx, hAe, _, _, hfree⟩ := h
  rw [hAe]
  show RefsIn S (familyIdx np (foldApps (.const f (canonL ar))
    (policyParameterLocals np (d + 1) ++ idx)))
  rw [familyIdx_directRec]
  exact fun e he r hr => (refs_of_free (hfree e he) (fun r' hr' =>
    hbA r' (hAe ▸ List.mem_append_right _
      (refs_foldApps_arg (List.mem_append_right _ he) hr')))) r hr

/-- `RefsIn` for a `FnRec` field's domain. -/
theorem refs_fnRec_dom {f ar np nq d : Nat} {A : Expr Nat}
    (h : FnRec f ar np nq d A) {S : Nat → Prop}
    (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = f) :
    ∀ r, r ∈ denRefs (piDom A) → S r := by
  obtain ⟨D', _, hAe, _, hD', _⟩ := h
  rw [hAe]
  show ∀ r, r ∈ denRefs (piDom (.pi D' _)) → S r
  exact fun r hr => (refs_of_free hD' (fun r' hr' =>
    hbA r' (hAe ▸ List.mem_append_left _ hr'))) r hr

section

variable (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} {S : Nat → Prop}
  (h : ∀ r, S r → ∀ ls, Equiv (μ₁ r ls) (μ₂ r ls))
include h

/-- `TelFits` agrees across tables when the telescope's references are in `S`
and the environments agree pointwise. -/
theorem TelFits_tablesOn (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → RefsIn S Ds →
    (ρ ρ' : Nat → PSet.{4}) → (∀ i, Equiv (ρ i) (ρ' i)) →
    (xs : List PSet.{4}) →
    (TelFits (mkM P μ₁) σ Ds ρ xs ↔ TelFits (mkM P μ₂) σ Ds ρ' xs)
  | [], _, _, _, _, [] => Iff.rfl
  | [], _, _, _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, _, _, [] => Iff.rfl
  | A :: Ds, hb, ρ, ρ', hρ, x :: xs => by
      show (x ∈ Ed _ (den _ σ ρ A) ∧ TelFits _ σ Ds (vcons x ρ) xs) ↔
        (x ∈ Ed _ (den _ σ ρ' A) ∧ TelFits _ σ Ds (vcons x ρ') xs)
      have e1 := ed_congr (mkM P μ₂)
        (den_tablesOn P h σ A (hb A (List.mem_cons_self _ _)) hρ)
      exact and_congr
        ⟨fun hx => mem_congr_right e1 hx, fun hx => mem_congr_right e1.symm hx⟩
        (TelFits_tablesOn σ Ds (fun e he => hb e (List.mem_cons_of_mem _ he))
          _ _ (fun i => vcons_congr Equiv.rfl hρ i) xs)

/-- `map`-`den` is pointwise-`LEq` across tables. -/
theorem LEq_map_den_tablesOn (σ : Nat → Nat) (ρ ρ' : Nat → PSet.{4})
    (hρ : ∀ i, Equiv (ρ i) (ρ' i)) : (es : List (Expr Nat)) → RefsIn S es →
    LEq (es.map (den (mkM P μ₁) σ ρ)) (es.map (den (mkM P μ₂) σ ρ'))
  | [], _ => trivial
  | e :: es, hb =>
      ⟨den_tablesOn P h σ e (hb e (List.mem_cons_self _ _)) hρ,
        LEq_map_den_tablesOn σ ρ ρ' hρ es
          (fun e' he' => hb e' (List.mem_cons_of_mem _ he'))⟩

/-- `argsFitF` agrees across tables. -/
theorem argsFitF_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (ρ ρ' : Nat → PSet.{4}) (hρ : ∀ i, Equiv (ρ i) (ρ' i))
    {A : Expr Nat} (hA : RefsIn S (appsSpine A).2) :
    argsFitF P μ₁ fd σ ρ A ↔ argsFitF P μ₂ fd σ ρ' A := by
  have h' : ∀ r, S r → ∀ ls, Equiv (μ₂ r ls) (μ₁ r ls) :=
    fun r hr ls => (h r hr ls).symm
  show TelFits (mkM P μ₁) σ _ ρ0 ((appsSpine A).2.map (den (mkM P μ₁) σ ρ)) ↔
    TelFits (mkM P μ₂) σ _ ρ0 ((appsSpine A).2.map (den (mkM P μ₂) σ ρ'))
  exact ⟨fun hf => TelFits_congr (mkM P μ₂) σ _ (fun _ => Equiv.rfl)
      (LEq_map_den_tablesOn P h σ ρ ρ' hρ _ hA)
      ((TelFits_tablesOn P h σ _ hpi ρ0 ρ0 (fun _ => Equiv.rfl) _).mp hf),
    fun hf => TelFits_congr (mkM P μ₁) σ _ (fun _ => Equiv.rfl)
      (LEq_map_den_tablesOn P h' σ ρ' ρ (fun i => (hρ i).symm) _ hA)
      ((TelFits_tablesOn P h' σ _ hpi ρ0 ρ0 (fun _ => Equiv.rfl) _).mp hf)⟩

/-- `resTupF` agrees across tables when the result indices' references are
in `S`. -/
theorem resTupF_tablesOn (σ : Nat → Nat)
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2) (ρp : Nat → PSet.{4}) (z : PSet.{4}) :
    Equiv (resTupF P μ₁ fd σ ρp z) (resTupF P μ₂ fd σ ρp z) := by
  unfold resTupF
  have hfi : findIdx (mkM P μ₁) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length =
      findIdx (mkM P μ₂) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length :=
by
    have hd : (mkM P μ₁).dec = (mkM P μ₂).dec := rfl
    exact findIdx_of_dec hd _ fd.ctors.length
  rw [hfi]
  cases hfj : findIdx (mkM P μ₂) (fun j => Equiv (tagOf z) (ord j)) fd.ctors.length with
  | none => exact Equiv.rfl
  | some j =>
      have hlt : j < fd.ctors.length := findIdx_lt _ _ hfj
      have hcm : fd.ctors.getD j ([], []) ∈ fd.ctors := by
        have : fd.ctors.getD j ([], []) = fd.ctors[j]'hlt := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt,
            Option.getD_some]
        rw [this]
        exact List.getElem_mem _
      exact ordPair_congr Equiv.rfl (tup_congr
        (LEq_map_den_tablesOn P h σ _ _
          (fun i => push_congr (LEq.refl _) (fun _ => Equiv.rfl) i) _
          (hrefs _ hcm)))

/-- `recTupAt` agrees across tables. -/
theorem recTupAt_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (ρ ρ' : Nat → PSet.{4}) (hρ : ∀ i, Equiv (ρ i) (ρ' i))
    {A : Expr Nat} (hA : RefsIn S (appsSpine A).2)
    (hidx : RefsIn S (familyIdx fd.params.length A)) :
    Equiv (recTupAt P μ₁ fd σ ρ A) (recTupAt P μ₂ fd σ ρ' A) := by
  unfold recTupAt
  exact cond_congr (argsFitF_tablesOn P h σ hpi ρ ρ' hρ hA)
    (ordPair_congr Equiv.rfl
      (tup_congr (LEq_map_den_tablesOn P h σ ρ ρ' hρ _ hidx))) Equiv.rfl

/-- `nonrecOkF` agrees across tables at a field whose references are in `S`. -/
theorem nonrecOkF_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) (x : PSet.{4})
    (hfield : ∀ r, r ∈ denRefs (fieldAt Fs k) → S r) :
    nonrecOkF P μ₁ fd σ ρp Fs k pre x ↔ nonrecOkF P μ₂ fd σ ρp Fs k pre x :=
  have e1 := truncW_congr (mkM P μ₂) W4 _ (ed_congr (mkM P μ₂)
    (den_tablesOn P h σ _ hfield (fun _ => Equiv.rfl)))
  ⟨fun hx => mem_congr_right e1 hx, fun hx => mem_congr_right e1.symm hx⟩

/-- `domEF` agrees across tables. -/
theorem domEF_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4})
    (hfield : ∀ r, r ∈ denRefs (piDom (fieldAt Fs k)) → S r) :
    Equiv (domEF P μ₁ σ ρp Fs k pre) (domEF P μ₂ σ ρp Fs k pre) :=
  ed_congr (mkM P μ₂)
    (den_tablesOn P h σ _ hfield (fun _ => Equiv.rfl))

/-- `domBigF` agrees across tables at a `.fn` field. -/
theorem domBigF_fn_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4})
    (hkf : kindOf fd.fref (fieldAt Fs k) = .fn)
    (hfield : ∀ r, r ∈ denRefs (piDom (fieldAt Fs k)) → S r) :
    Equiv (domBigF P μ₁ fd σ ρp Fs k pre) (domBigF P μ₂ fd σ ρp Fs k pre) := by
  unfold domBigF
  rw [hkf]
  have e1 := domEF_tablesOn P h σ ρp Fs k pre hfield
  exact cond_congr
    ⟨fun hm => mem_congr_left e1 hm, fun hm => mem_congr_left e1.symm hm⟩
    e1 Equiv.rfl

/-- `recTupF` agrees across tables at a `.fn` field. -/
theorem recTupF_fn_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices)) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4})
    (hkf : kindOf fd.fref (fieldAt Fs k) = .fn)
    (hdom : ∀ r, r ∈ denRefs (piDom (fieldAt Fs k)) → S r)
    (hcod : RefsIn S (appsSpine (piCod (fieldAt Fs k))).2)
    (hcodi : RefsIn S (familyIdx fd.params.length (piCod (fieldAt Fs k))))
    (y : PSet.{4}) :
    Equiv (recTupF P μ₁ fd σ ρp Fs k pre y)
      (recTupF P μ₂ fd σ ρp Fs k pre y) := by
  unfold recTupF
  rw [hkf]
  have e1 := domEF_tablesOn P h σ ρp Fs k pre hdom
  exact cond_congr
    ⟨fun hm => mem_congr_left e1 hm, fun hm => mem_congr_left e1.symm hm⟩
    (recTupAt_tablesOn P h σ hpi _ _
      (fun i => vcons_congr Equiv.rfl (fun _ => Equiv.rfl) i)
      hcod hcodi) Equiv.rfl

/-- `recTupF` agrees across tables at a non-`.fn` field. -/
theorem recTupF_direct_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices)) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4})
    (hkd : kindOf fd.fref (fieldAt Fs k) = .direct)
    (hA : RefsIn S (appsSpine (fieldAt Fs k)).2)
    (hAi : RefsIn S (familyIdx fd.params.length (fieldAt Fs k)))
    (y : PSet.{4}) :
    Equiv (recTupF P μ₁ fd σ ρp Fs k pre y)
      (recTupF P μ₂ fd σ ρp Fs k pre y) := by
  unfold recTupF
  rw [hkd]
  exact recTupAt_tablesOn P h σ hpi _ _ (fun _ => Equiv.rfl) hA hAi

/-- `InPhi` for `semF` agrees across tables along a class-A telescope. -/
theorem InPhi_semF_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (ρp : Nat → PSet.{4}) (X : PSet.{4}) :
    ∀ (done rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest done.length →
      (∀ e, e ∈ done ++ rest → ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref) →
      (Sem.InPhi (semF P μ₁ fd σ ρp (done ++ rest)) X
          (kindsOf fd.fref rest) xs done.length pre →
        Sem.InPhi (semF P μ₂ fd σ ρp (done ++ rest)) X
          (kindsOf fd.fref rest) xs done.length pre) := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs _ _
      cases xs with
      | nil => exact fun h => h
      | cons x xs' => exact fun h => h
  | cons A rest' ih =>
      intro pre xs hdisj hb
      obtain ⟨hdisjA, hcls'⟩ := hdisj
      have hf : fieldAt (done ++ A :: rest') done.length = A := by
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      have hbA := hb A (List.mem_append.mpr (Or.inr (List.mem_cons_self _ _)))
      have hb' : ∀ e, e ∈ done ++ [A] ++ rest' → ∀ r, r ∈ denRefs e →
          S r ∨ r = fd.fref := fun e he r hr => by
        have he' : e ∈ done ++ A :: rest' := by
          rw [List.append_assoc] at he
          exact he
        exact hb e he' r hr
      rcases hdisjA with hfr | hdr | hfn
      · simp only [kindsOf, List.map, kindOf_free hfr]
        cases xs with
        | nil => exact fun h => False.elim h
        | cons x xs' =>
            have hih := ih (done ++ [A]) (pre ++ [x]) xs' (by simpa using hcls') hb'
            have hlen : (done ++ [A]).length = done.length + 1 := by simp
            have hih' := hlen.symm ▸ hih
            have hf2 : fieldAt (done ++ [A] ++ rest') done.length = A := by
              rw [List.append_assoc]; exact hf
            show (semF P μ₁ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.plain :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre →
              (semF P μ₂ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.plain :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre
            rw [← List.append_assoc]
            refine fun ⟨hx, hin⟩ => ⟨?_, hih' hin⟩
            have hfield : ∀ r, r ∈ denRefs
                (fieldAt (done ++ [A] ++ rest') done.length) → S r := by
              rw [hf2]
              exact refs_of_free hfr hbA
            exact (nonrecOkF_tablesOn P h σ ρp _ _ _ _ hfield).mp hx
      · simp only [kindsOf, List.map, kindOf_directRec hdr]
        cases xs with
        | nil => exact fun h => False.elim h
        | cons x xs' =>
            have hih := ih (done ++ [A]) (pre ++ [x]) xs' (by simpa using hcls') hb'
            have hlen : (done ++ [A]).length = done.length + 1 := by simp
            have hih' := hlen.symm ▸ hih
            have hf2 : fieldAt (done ++ [A] ++ rest') done.length = A := by
              rw [List.append_assoc]; exact hf
            show (semF P μ₁ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.direct :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre →
              (semF P μ₂ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.direct :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre
            rw [← List.append_assoc]
            refine fun ⟨⟨hxm, hxe⟩, hin⟩ => ⟨⟨hxm, ?_⟩, hih' hin⟩
            have e1 := resTupF_tablesOn P h σ hrefs ρp x
            have hkd : kindOf fd.fref (fieldAt (done ++ [A] ++ rest') done.length) =
                .direct := by rw [hf2]; exact kindOf_directRec hdr
            have hArgs : RefsIn S
                (appsSpine (fieldAt (done ++ [A] ++ rest') done.length)).2 := by
              rw [hf2]; exact refs_directRec_args hdr hbA
            have hAi : RefsIn S
                (familyIdx fd.params.length
                  (fieldAt (done ++ [A] ++ rest') done.length)) := by
              rw [hf2]; exact refs_directRec_familyIdx hdr hbA
            have e2 := recTupF_direct_tablesOn P h σ hpi ρp
              (done ++ [A] ++ rest') done.length pre hkd hArgs hAi (y := pempty)
            have e2' : Equiv
                ((semF P μ₁ fd σ ρp (done ++ [A] ++ rest')).recTup done.length pre pempty)
                ((semF P μ₂ fd σ ρp (done ++ [A] ++ rest')).recTup done.length pre pempty) := e2
            exact (e1.symm.trans hxe).trans e2' 
      · simp only [kindsOf, List.map, kindOf_fnRec hfn]
        cases xs with
        | nil => exact fun h => False.elim h
        | cons x xs' =>
            have hih := ih (done ++ [A]) (pre ++ [x]) xs' (by simpa using hcls') hb'
            have hlen : (done ++ [A]).length = done.length + 1 := by simp
            have hih' := hlen.symm ▸ hih
            have hf2 : fieldAt (done ++ [A] ++ rest') done.length = A := by
              rw [List.append_assoc]; exact hf
            show (semF P μ₁ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.fn :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre →
              (semF P μ₂ fd σ ρp (done ++ ([A] ++ rest'))).InPhi X
              (PKind.fn :: List.map (kindOf fd.fref) rest') (x :: xs') done.length pre
            rw [← List.append_assoc]
            refine fun ⟨hxm, hin⟩ => ⟨?_, hih' hin⟩
            have hdom : ∀ r, r ∈ denRefs
                (piDom (fieldAt (done ++ [A] ++ rest') done.length)) → S r := by
              rw [hf2]; exact refs_fnRec_dom hfn hbA
            have hcod : RefsIn S
                (appsSpine (piCod (fieldAt (done ++ [A] ++ rest') done.length))).2 := by
              rw [hf2]; exact refs_fnRec_args hfn hbA
            have hcodi : RefsIn S
                (familyIdx fd.params.length
                  (piCod (fieldAt (done ++ [A] ++ rest') done.length))) := by
              rw [hf2]; exact refs_fnRec_familyIdx hfn hbA
            have hkf : kindOf fd.fref (fieldAt (done ++ [A] ++ rest') done.length) = .fn := by
              rw [hf2]; exact kindOf_fnRec hfn
            have e1 := domBigF_fn_tablesOn P h σ ρp (done ++ [A] ++ rest') done.length pre
              hkf hdom
            have e2 : ∀ y y', Equiv y y' →
                Equiv (Sem.fib (semF P μ₁ fd σ ρp (done ++ [A] ++ rest')) X done.length pre y)
                  (Sem.fib (semF P μ₂ fd σ ρp (done ++ [A] ++ rest')) X done.length pre y') := by
              intro y y' hy
              show Equiv (sep _ X) (sep _ X)
              have er := resTupF_tablesOn P h σ hrefs ρp
              have ec : Equiv
                  (recTupF P μ₁ fd σ ρp (done ++ [A] ++ rest') done.length pre y)
                  (recTupF P μ₂ fd σ ρp (done ++ [A] ++ rest') done.length pre y') :=
                (recTupF_fn_tablesOn P h σ hpi ρp _ done.length pre
                  hkf hdom hcod hcodi y).trans
                  (recTupF_congr P μ₂ fd σ ρp _ done.length (LEq.refl pre) hy)
              exact sep_congr
                (fun a b hab hz =>
                  ((er b).symm.trans
                    ((resTupF_congr P μ₁ fd σ ρp hab.symm).trans hz)).trans ec)
                (fun a b hab hz =>
                  (((er b).trans
                      (resTupF_congr P μ₂ fd σ ρp hab.symm)).trans hz).trans ec.symm)
                Equiv.rfl
            exact mem_piSet_of_dep
              (fun y y' hy => Sem.fib_resp (semF P μ₂ fd σ ρp (done ++ [A] ++ rest')) X
                done.length pre hy)
              (isFuncOnDep_equiv e1 e2 (Equiv.refl x)
                (isFuncOnDep_of_mem_piSet
                  (fun y y' hy => Sem.fib_resp (semF P μ₁ fd σ ρp (done ++ [A] ++ rest')) X
                    done.length pre hy) hxm))

/-- `PsiF` agrees across tables when all constructor expressions are
`S ∪ {fref}`-referenced and the fields are class-A. -/
theorem PsiF_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    {X : PSet.{4}} :
    Equiv (PsiF P μ₁ fd σ ρp X) (PsiF P μ₂ fd σ ρp X) := by
  have h' : ∀ r, S r → ∀ ls, Equiv (μ₂ r ls) (μ₁ r ls) :=
    fun r hr ls => (h r hr ls).symm
  unfold PsiF
  exact sep_congr
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_tablesOn P h σ hpi hrefs ρp X [] c.1 [] xs (hclsA c (List.getElem?_mem hcj))
        (fun e he => hb c (List.getElem?_mem hcj) e he) hIn⟩)
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_tablesOn P h' σ hpi hrefs ρp X [] c.1 [] xs (hclsA c (List.getElem?_mem hcj))
        (fun e he => hb c (List.getElem?_mem hcj) e he) hIn⟩)
    Equiv.rfl

/-- `DStar` agrees across tables. -/
theorem DStar_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hN₁ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₁ σ ρp fd.fref (fd.ctors.get j).1)
    (hN₂ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₂ σ ρp fd.fref (fd.ctors.get j).1)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0) :
    Equiv (DStar P μ₁ fd σ ρp) (DStar P μ₂ fd σ ρp) := by
  cases hkk : evalTotal σ fd.resLevel with
  | zero =>
      rw [DStar_zero P μ₁ fd σ ρp hkk, DStar_zero P μ₂ fd σ ρp hkk]
      exact Equiv.rfl
  | succ n =>
      have hk : evalTotal σ fd.resLevel ≠ 0 := by rw [hkk]; exact Nat.succ_ne_zero n
      exact IsLfp.unique_of_congr (fun X => PsiF_tablesOn P h σ ρp hpi hrefs hb hclsA)
        (DStar_lfp P μ₁ fd σ ρp hk (hN₁ σ ρp)).1 (DStar_lfp P μ₂ fd σ ρp hk (hN₂ σ ρp)).1

/-- `fibAt` agrees across tables. -/
theorem fibAt_tablesOn (σ : Nat → Nat)
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2) (ρp : Nat → PSet.{4})
    (is : List PSet.{4})
    (hD : Equiv (DStar P μ₁ fd σ ρp) (DStar P μ₂ fd σ ρp)) :
    Equiv (fibAt P μ₁ fd (DStar P μ₁ fd) σ ρp is)
      (fibAt P μ₂ fd (DStar P μ₂ fd) σ ρp is) := by
  have er := resTupF_tablesOn P h σ hrefs ρp
  exact sep_congr
    (fun a b hab hz => ((er b).symm.trans
      (resTupF_congr P μ₁ fd σ ρp hab.symm)).trans hz)
    (fun a b hab hz => ((er b).trans
      (resTupF_congr P μ₂ fd σ ρp hab.symm)).trans hz)
    hD

/-- `famEndD` agrees across tables. -/
theorem famEndD_tablesOn (σ : Nat → Nat)
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hD : ∀ ρ : Nat → PSet.{4},
      Equiv (DStar P μ₁ fd σ (shiftρ fd.indices.length ρ))
        (DStar P μ₂ fd σ (shiftρ fd.indices.length ρ))) (ρ : Nat → PSet.{4}) :
    Equiv (famEndD P μ₁ fd (DStar P μ₁ fd) σ ρ)
      (famEndD P μ₂ fd (DStar P μ₂ fd) σ ρ) :=
  tyv_congr (fibAt_tablesOn P h σ hrefs _ _ (hD ρ))

/-- `famLfp` agrees across tables. -/
theorem famLfp_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hN₁ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₁ σ ρp fd.fref (fd.ctors.get j).1)
    (hN₂ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₂ σ ρp fd.fref (fd.ctors.get j).1)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (vs : List Nat) :
    Equiv (famLfp P μ₁ fd vs) (famLfp P μ₂ fd vs) := by
  show Equiv (piLam (mkM P μ₁) _ _ ρ0 _) (piLam (mkM P μ₂) _ _ ρ0 _)
  exact piLam_tablesOn P h _
    (famEndD_envResp P μ₁ fd _ (fun σ' ρ ρ' hρ => DStar_env P μ₁ fd (hN₁) σ' hρ) _)
    (fun ρ => famEndD_tablesOn P h _ hrefs
      (fun ρ' => DStar_tablesOn P h _ (shiftρ fd.indices.length ρ') hN₁ hN₂
        hpi hrefs hb hclsA) ρ)
    _ (famType_refs fd hpi) ρ0

/-- `okP` agrees across tables. -/
theorem okP_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    {T₁ T₂ : PSet.{4}} (hT : Equiv T₁ T₂)
    (ρ ρ' : Nat → PSet.{4}) (hρ : ∀ i, Equiv (ρ i) (ρ' i))
    {A : Expr Nat} (hbA : ∀ r, r ∈ denRefs A → S r ∨ r = fd.fref)
    (d : Nat)
    (hdisj : occursConst fd.fref A = false ∨
      DirectRec fd.fref ar fd.params.length fd.indices.length d A ∨
      FnRec fd.fref ar fd.params.length fd.indices.length d A)
    (x : PSet.{4}) :
    okP P μ₁ fd T₁ σ ρ A x ↔ okP P μ₂ fd T₂ σ ρ' A x := by
  have h' : ∀ r, S r → ∀ ls, Equiv (μ₂ r ls) (μ₁ r ls) :=
    fun r hr ls => (h r hr ls).symm
  rcases hdisj with hfree | hdr | hfn
  · simp only [okP, kindOf_free hfree]
    show (x ∈ Ed _ (den _ σ ρ A)) ↔ (x ∈ Ed _ (den _ σ ρ' A))
    have e1 := ed_congr (mkM P μ₂)
      (den_tablesOn P h σ A (refs_of_free hfree hbA) hρ)
    exact ⟨fun hx => mem_congr_right e1 hx, fun hx => mem_congr_right e1.symm hx⟩
  · simp only [okP, kindOf_directRec hdr]
    have hargs := refs_directRec_args hdr hbA
    have hidx := refs_directRec_familyIdx hdr hbA
    have ht : tup ((familyIdx fd.params.length A).map (den (mkM P μ₁) σ ρ)) ∈ T₁ ↔
        tup ((familyIdx fd.params.length A).map (den (mkM P μ₂) σ ρ')) ∈ T₂ :=
      ⟨fun hm => mem_congr_right hT
        (mem_congr_left (tup_congr (LEq_map_den_tablesOn P h σ ρ ρ' hρ _ hidx)) hm),
       fun hm => mem_congr_right hT.symm
        (mem_congr_left (tup_congr (LEq_map_den_tablesOn P h' σ ρ' ρ
          (fun i => (hρ i).symm) _ hidx)) hm)⟩
    exact and_congr Iff.rfl
      (and_congr (argsFitF_tablesOn P h σ hpi ρ ρ' hρ hargs) ht)
  · simp only [okP, kindOf_fnRec hfn]
    have hdom := refs_fnRec_dom hfn hbA
    have hcod := refs_fnRec_args hfn hbA
    have hcodi := refs_fnRec_familyIdx hfn hbA
    have e1 := ed_congr (mkM P μ₂)
      (den_tablesOn P h σ (piDom A) hdom hρ)
    have h'env : ∀ y : PSet.{4}, ∀ i,
        Equiv (vcons y ρ i) (vcons y ρ' i) := fun y i => vcons_congr Equiv.rfl hρ i
    refine and_congr Iff.rfl ⟨?_, ?_⟩
    · intro hyf y hym
      obtain ⟨hf, ht⟩ := hyf y (mem_congr_right e1.symm hym)
      exact ⟨(argsFitF_tablesOn P h σ hpi _ _ (h'env y) hcod).mp hf,
        mem_congr_right hT (mem_congr_left (tup_congr
          (LEq_map_den_tablesOn P h σ _ _ (h'env y) _ hcodi)) ht)⟩
    · intro hyf y hym
      obtain ⟨hf, ht⟩ := hyf y (mem_congr_right e1 hym)
      exact ⟨(argsFitF_tablesOn P h' σ hpi _ _
          (fun i => vcons_congr Equiv.rfl (fun j => (hρ j).symm) i) hcod).mp hf,
        mem_congr_right hT.symm (mem_congr_left (tup_congr
          (LEq_map_den_tablesOn P h' σ _ _
            (fun i => vcons_congr Equiv.rfl (fun j => (hρ j).symm) i) _ hcodi)) ht)⟩

/-- `TelFitsP` agrees across tables. -/
theorem TelFitsP_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    {T₁ T₂ : PSet.{4}} (hT : Equiv T₁ T₂) :
    ∀ (rest : List (Expr Nat)) (d : Nat) (ρ ρ' : Nat → PSet.{4})
      (xs : List PSet.{4}),
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest d →
      (∀ e, e ∈ rest → ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref) →
      (∀ i, Equiv (ρ i) (ρ' i)) →
      (TelFitsP P μ₁ fd T₁ σ rest ρ xs ↔ TelFitsP P μ₂ fd T₂ σ rest ρ' xs) := by
  intro rest
  induction rest with
  | nil =>
      intro d ρ ρ' xs _ _ _
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs' => exact Iff.rfl
  | cons A rest' ih =>
      intro d ρ ρ' xs hcls hb hρ
      obtain ⟨hdisjA, hcls'⟩ := hcls
      have hbA := hb A (List.mem_cons_self _ _)
      have hb' : ∀ e, e ∈ rest' → ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref :=
        fun e he => hb e (List.mem_cons_of_mem _ he)
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs' =>
          show (okP P μ₁ fd T₁ σ ρ A x ∧ TelFitsP _ _ _ T₁ σ rest' (vcons x ρ) xs') ↔
            (okP P μ₂ fd T₂ σ ρ' A x ∧ TelFitsP _ _ _ T₂ σ rest' (vcons x ρ') xs')
          have hok := okP_tablesOn P h σ hpi hrefs hT ρ ρ' hρ hbA d hdisjA x
          exact and_congr hok
            (ih (d + 1) (vcons x ρ) (vcons x ρ') xs' hcls' hb'
              (fun i => vcons_congr Equiv.rfl hρ i))

/-- `FitSetU` agrees across tables. -/
theorem FitSetU_tablesOn (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) → RefsIn S Ds →
    (ρ ρ' : Nat → PSet.{4}) → (∀ i, Equiv (ρ i) (ρ' i)) →
    Equiv (FitSetU (mkM P μ₁) σ Ds ρ) (FitSetU (mkM P μ₂) σ Ds ρ')
  | [], _, _, _, _ => Equiv.rfl
  | A :: Ds, hb, ρ, ρ', hρ => sUnion_congr (sImage_congr
      (fun a a' haa => sImage_congr (fun b b' hbb =>
        ordPair_congr haa hbb) (FitSetU_tablesOn σ Ds
          (fun e he => hb e (List.mem_cons_of_mem _ he)) _ _
          (fun i => vcons_congr haa hρ i)))
      (ed_congr (mkM P μ₂)
        (den_tablesOn P h σ A (hb A (List.mem_cons_self _ _)) hρ)))

/-- `PhiP` agrees across tables. -/
theorem PhiP_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    {T₁ T₂ : PSet.{4}} (hT : Equiv T₁ T₂) :
    Equiv (PhiP P μ₁ fd σ ρp T₁) (PhiP P μ₂ fd σ ρp T₂) := by
  have h' : ∀ r, S r → ∀ ls, Equiv (μ₂ r ls) (μ₁ r ls) :=
    fun r hr ls => (h r hr ls).symm
  unfold PhiP
  exact sep_congr (fun a b hab ⟨j, c, xs, hcj, hf, ht⟩ =>
      ⟨j, c, xs, hcj,
        (TelFitsP_tablesOn P h σ hpi hrefs hT c.1 0 ρp ρp xs
          (hclsA c (List.getElem?_mem hcj))
          (fun e he => hb c (List.getElem?_mem hcj) e he)
          (fun _ => Equiv.rfl)).mp hf,
        (hab.symm.trans (ht.trans (tup_congr (LEq_map_den_tablesOn P h σ (push xs ρp) (push xs ρp)
          (fun i => push_congr (LEq.refl _) (fun _ => Equiv.rfl) i) _
          (hrefs c (List.getElem?_mem hcj))))))⟩)
    (fun a b hab ⟨j, c, xs, hcj, hf, ht⟩ =>
      ⟨j, c, xs, hcj,
        (TelFitsP_tablesOn P h' σ hpi hrefs hT.symm c.1 0 ρp ρp xs
          (hclsA c (List.getElem?_mem hcj))
          (fun e he => hb c (List.getElem?_mem hcj) e he)
          (fun _ => Equiv.rfl)).mp hf,
        (hab.symm.trans (ht.trans (tup_congr (LEq_map_den_tablesOn P h' σ (push xs ρp) (push xs ρp)
          (fun i => push_congr (LEq.refl _) (fun _ => Equiv.rfl) i) _
          (hrefs c (List.getElem?_mem hcj))))))⟩)
    (FitSetU_tablesOn P h σ fd.indices
      (fun e he => hpi e (List.mem_append_right _ he)) ρp ρp (fun _ => Equiv.rfl))

/-- `DStarP` agrees across tables. -/
theorem DStarP_tablesOn (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0) :
    Equiv (DStarP P μ₁ fd σ ρp) (DStarP P μ₂ fd σ ρp) :=
  IsLfp.unique_of_congr
    (fun T => PhiP_tablesOn P h σ ρp hpi hrefs hb hclsA (Equiv.refl T))
    (DStarP_isLfp P μ₁ fd σ ρp) (DStarP_isLfp P μ₂ fd σ ρp)

/-- `famEndP` agrees across tables. -/
theorem famEndP_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (ρ : Nat → PSet.{4}) :
    Equiv (famEndP P μ₁ fd σ ρ) (famEndP P μ₂ fd σ ρ) := by
  show Equiv (tyv (tv (tup _ ∈ _))) (tyv (tv (tup _ ∈ _)))
  exact tyv_congr (tv_congr
    ⟨fun hm => mem_congr_right
      (DStarP_tablesOn P h σ (shiftρ fd.indices.length ρ) hpi hrefs hb hclsA) hm,
     fun hm => mem_congr_right
      (DStarP_tablesOn P h σ (shiftρ fd.indices.length ρ) hpi hrefs hb hclsA).symm hm⟩)

/-- `famLfpP` agrees across tables. -/
theorem famLfpP_tablesOn (σ : Nat → Nat)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2)
    (hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (vs : List Nat) :
    Equiv (famLfpP P μ₁ fd vs) (famLfpP P μ₂ fd vs) := by
  show Equiv (piLam (mkM P μ₁) _ _ ρ0 _) (piLam (mkM P μ₂) _ _ ρ0 _)
  exact piLam_tablesOn P h _ (famEndP_envResp P μ₁ fd _)
    (fun ρ => famEndP_tablesOn P h _ hpi hrefs hb hclsA ρ)
    _ (famType_refs fd hpi) ρ0

/-- The combined family entry `famKT` reads the table only at the family's
references. -/
theorem famKT_agreeOn
    (hN₁ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₁ σ ρp fd.fref (fd.ctors.get j).1)
    (hN₂ : ∀ σ ρp (j : Fin fd.ctors.length),
      NonIRSem P μ₂ σ ρp fd.fref (fd.ctors.get j).1)
    (hpi : RefsIn S (fd.params ++ fd.indices))
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (hfam : FamRefsIn (fun r => S r ∨ r = fd.fref) fd)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (vs : List Nat) :
    Equiv (famKT P μ₁ fd vs) (famKT P μ₂ fd vs) := by
  have hrefs : ∀ c, c ∈ fd.ctors → RefsIn S c.2 := fun c hc e he r hr =>
    (refs_of_free (hri c hc e he) (fun r' hr' =>
      (hfam c hc).2 e he r' hr')) r hr
  have hb : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.1 →
      ∀ r, r ∈ denRefs e → S r ∨ r = fd.fref :=
    fun c hc e he => (hfam c hc).1 e he
  show Equiv (if evalTotal (σOf vs) fd.resLevel = 0 then famLfpP P μ₁ fd vs
      else famLfp P μ₁ fd vs)
    (if evalTotal (σOf vs) fd.resLevel = 0 then famLfpP P μ₂ fd vs
      else famLfp P μ₂ fd vs)
  by_cases hk0 : evalTotal (σOf vs) fd.resLevel = 0
  · rw [if_pos hk0, if_pos hk0]
    exact famLfpP_tablesOn P h (σOf vs) hpi hrefs hb hclsA vs
  · rw [if_neg hk0, if_neg hk0]
    exact famLfp_tablesOn P h (σOf vs) ρ0 hN₁ hN₂ hpi hrefs hb hclsA vs
