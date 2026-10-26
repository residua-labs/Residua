import rcic.RcicF3KTWRec

open Rcic.Declarative

/-!
# KT-3b: recursor membership at the `famKT` table, by `DStar` induction

Helpers toward `recVal_mem_rec_KT`: a `≈`-table variant of `TelFits_den_iff`
and `TelFitsT → TelFits`.
-/

namespace Rcic.F3.PSet

/-- `TelFits` respects pointwise-`≈` tables. -/
theorem TelFits_tables_equiv (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}}
    (h : ∀ r ls, Equiv (μ₁ r ls) (μ₂ r ls)) (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) →
    ∀ ρ xs, TelFits (mkM P μ₁) σ Ds ρ xs ↔ TelFits (mkM P μ₂) σ Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil => intro ρ xs; cases xs <;> exact Iff.rfl
  | cons A rest ih =>
      intro ρ xs
      cases xs with
      | nil => exact Iff.rfl
      | cons x xs' =>
          show (x ∈ Ed _ (den _ σ ρ A) ∧ TelFits _ σ rest (vcons x ρ) xs') ↔
            (x ∈ Ed _ (den _ σ ρ A) ∧ TelFits _ σ rest (vcons x ρ) xs')
          have e1 := ed_congr (mkM P μ₂)
            (den_tables P h σ A (ρ := ρ) (ρ' := ρ) (fun _ => Equiv.rfl))
          exact and_congr ⟨fun hx => mem_congr_right e1 hx,
              fun hx => mem_congr_right e1.symm hx⟩ (ih _ _)

/-- `TelFitsT` is `TelFits` plus the stage truncation; the untruncated claim
follows directly. -/
theorem TelFitsT_telFits (M : Interp.{4}) (W : Nat → PSet.{4}) (k : Nat)
    (σ : Nat → Nat) :
    (Ds : List (Expr Nat)) →
    ∀ ρ xs, TelFitsT M W k σ Ds ρ xs → TelFits M σ Ds ρ xs := by
  intro Ds
  induction Ds with
  | nil => intro ρ xs h; cases xs <;> trivial
  | cons A rest ih =>
      intro ρ xs h
      cases xs with
      | nil => exact h
      | cons x xs' =>
          obtain ⟨hx, hfs⟩ := h
          exact ⟨truncW_sub hx, ih _ _ hfs⟩

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4})
  {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m) (G : RecGroup a)
  (vs : List Nat)
  (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
  (hpsl : ps.length = a.family.parameters.length)

/-- The motive predicate is `≈`-invariant. -/
theorem motive_pred_resp
    (x x' : PSet.{4}) (hxx : Equiv x x')
    (hz : ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x) (ordPair pempty (tup idxv)) →
      recCore (mkM P μ) (famDataOf a) ms x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x]))) :
    ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x') (ordPair pempty (tup idxv)) →
      recCore (mkM P μ) (famDataOf a) ms x' ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x'])) := by
  intro idxv hl hfit hre
  have hre' : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x)
      (ordPair pempty (tup idxv)) :=
    (resTupF_congr P μ (famDataOf a) (σOf vs) (push ps ρ0) hxx).trans hre
  have hm := hz idxv hl hfit hre'
  exact mem_congr_right (ed_congr (mkM P μ)
    (fapps_congr_args mo (LEq_append (LEq.refl idxv) (show LEq [x] [x'] from ⟨hxx, trivial⟩))))
    (mem_congr_left (recCore_resp _ _ _ x x' hxx) hm)

/-- The walk lemma: `InPhi` over a candidate set `Z` whose predicate is the
motive condition gives `IHOkF`. -/
theorem ihOkF_of_InPhi (Z : PSet.{4})
    (hZ : ∀ x, x ∈ Z → ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x) (ordPair pempty (tup idxv)) →
      recCore (mkM P μ) (famDataOf a) ms x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])))
    (hps : ps.length = (famDataOf a).params.length)
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClass (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
        (famDataOf a).indices.length rest done.length →
      Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
        (kindsOf (famDataOf a).fref rest) xs done.length pre →
      IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
        (recCore (mkM P μ) (famDataOf a) ms) (famDataOf a).fref rest
        (push pre (push ps ρ0)) xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls hIn
      cases xs with
      | nil => trivial
      | cons x xs' =>
          exact Nat.noConfusion (Sem.InPhi.length _ _ _ _ _ hIn)
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls hIn
      obtain ⟨hdisj, hcls'⟩ := hcls
      have hf : fieldAt Fs done.length = A := by
        rw [hFs]
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      show IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
        (recCore (mkM P μ) (famDataOf a) ms) (famDataOf a).fref (A :: rest')
        (push pre (push ps ρ0)) xs
      cases xs with
      | nil =>
          exact Nat.noConfusion (Sem.InPhi.length _ _ _ _ _ hIn)
      | cons x xs' =>
          rcases hdisj with h0 | hdr
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_free h0] at hIn
            obtain ⟨hx, hin⟩ := hIn
            refine ⟨fun ho => ?_, ih_step done A rest' pre x xs' hFs hpre hcls' IH hin⟩
            rw [h0] at ho; cases ho
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_directRec hdr] at hIn
            obtain ⟨⟨hxm, hxe⟩, hin⟩ := hIn
            refine ⟨fun ho => ?_, ih_step done A rest' pre x xs' hFs hpre hcls' IH hin⟩
            obtain ⟨idx, hAe, hlen, hfree⟩ := hdr
            have hrecD : (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs).recTup
                done.length pre pempty =
                recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A := by
              show recTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs
                  done.length pre pempty = _
              unfold recTupF
              rw [hf, kindOf_directRec ⟨idx, hAe, hlen, hfree⟩]
            rw [hrecD] at hxe
            have haf : argsFitF P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A := by
              cases hdec : P.dec (argsFitF P μ (famDataOf a) (σOf vs)
                (push pre (push ps ρ0)) A) with
              | isTrue h => exact h
              | isFalse hn =>
                  exfalso
                  have hs : recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A =
                      singleton pempty := by unfold recTupAt; rw [cond_neg hn]
                  exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs) (push ps ρ0) x
                    (hxe.trans (by rw [← hs]; exact Equiv.rfl))
            have hre : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x)
                (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                  (push pre (push ps ρ0)))))) := by
              have hre2 : recTupAt P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0)) A =
                  ordPair pempty (tup ((familyIdx (famDataOf a).params.length A).map
                    (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))) := by
                unfold recTupAt; rw [cond_pos haf]
              rw [hAe, familyIdx_directRec] at hre2
              have hse : Equiv (recTupAt P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0)) A)
                  (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                    (push pre (push ps ρ0)))))) := by
                rw [← hre2, hAe]
                exact Equiv.rfl
              exact hxe.trans hse
            have hTf : TelFits (mkM P μ) (σOf vs)
                ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                ((policyParameterLocals (famDataOf a).params.length done.length ++ idx).map
                  (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)))) := by
              rw [hAe] at haf
              exact (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                (push pre (push ps ρ0)) (famDataOf a).fref
                (canonL a.family.member.arity) _).mp haf
            have hpsl' : ps.length = (famDataOf a).params.length := hps
            have e := den_recArgs (mkM P μ) (σOf vs) ps pre idx
            rw [hpre] at e
            rw [← hpsl'] at hTf
            rw [e] at hTf
            obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
            obtain ⟨rfl, rfl⟩ := List.append_inj heq
              (by rw [TelFits.length h1]; exact hpsl')
            rw [hAe, ihAt_foldApps (fun _ _ h => Expr.noConfusion h), familyIdx_directRec]
            exact hZ x hxm (idx.map (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))
              (by rw [List.length_map]; exact hlen) h2 hre
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClass (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest' (done.length + 1))
        (IH : ∀ (done : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done ++ rest' → pre.length = done.length →
          FieldsClass (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
            (famDataOf a).indices.length rest' done.length →
          Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
            (kindsOf (famDataOf a).fref rest') xs done.length pre →
          IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
            (recCore (mkM P μ) (famDataOf a) ms) (famDataOf a).fref rest'
            (push pre (push ps ρ0)) xs)
        (hin : Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0) Fs) Z
          (kindsOf (famDataOf a).fref rest') xs' (done.length + 1) (pre ++ [x])) :
        IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
          (recCore (mkM P μ) (famDataOf a) ms) (famDataOf a).fref rest'
          (vcons x (push pre (push ps ρ0))) xs' := by
      have hFs' : Fs = (done ++ [A]) ++ rest' := by rw [hFs]; simp [List.append_assoc]
      have hpre' : (pre ++ [x]).length = (done ++ [A]).length := by simp [hpre]
      have hcls'' : FieldsClass (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest'
          (done ++ [A]).length := by
        rw [List.length_append, List.length_singleton]; exact hcls'
      have hin' : Sem.InPhi (semF P μ (famDataOf a) (σOf vs) (push ps ρ0)
          Fs) Z (kindsOf (famDataOf a).fref rest') xs'
          (done ++ [A]).length (pre ++ [x]) :=
        (show (done ++ [A]).length = done.length + 1 by simp) ▸ hin
      have h1 : vcons x (push pre (push ps ρ0)) = push (pre ++ [x]) (push ps ρ0) := by
        rw [push_append]; rfl
      rw [h1]
      exact IH (done ++ [A]) (pre ++ [x]) xs' hFs' hpre' hcls'' hin'
include G hpsl
/-- Every element of `DStar` satisfies the motive condition — the `DStar`
induction for the recursor's membership. -/
theorem DStar_motive
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0) :
    ∀ x, x ∈ DStar P μ (famDataOf a) (σOf vs) (push ps ρ0) →
      ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
        TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
        Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x) (ordPair pempty (tup idxv)) →
        recCore (mkM P μ) (famDataOf a) ms x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  have hpf : ∀ e, e ∈ (famDataOf a).params ++ (famDataOf a).indices →
      occursConst (famDataOf a).fref e = false := G.famFree
  let σ := σOf vs
  let fd := famDataOf a
  let ρp := push ps ρ0
  let p : PSet.{4} → Prop := fun z => ∀ idxv : List PSet.{4},
    idxv.length = (famDataOf a).indices.length →
    TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
    Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) z) (ordPair pempty (tup idxv)) →
    recCore (mkM P μ) (famDataOf a) ms z ∈ Ed (mkM P μ) (fapps mo (idxv ++ [z]))
  let Z := sep p (DStar P μ fd σ ρp)
  have hZD : Sub Z (DStar P μ fd σ ρp) := fun w hw => mem_sep_subset hw
  have hZ : ∀ x, x ∈ Z → ∀ idxv : List PSet.{4},
      idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x) (ordPair pempty (tup idxv)) →
      recCore (mkM P μ) (famDataOf a) ms x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])) :=
    fun x hx idxv hl hfit hre => by
      obtain ⟨i, hpi, hxi⟩ := mem_sep.mp hx
      exact (motive_pred_resp P μ a vs ps mo ms _ x hxi hpi) idxv hl hfit hre
  have hsub : Sub (PsiF P μ fd σ ρp Z) Z := by
    intro z hz
    obtain ⟨i, ⟨j, c, xs, hcj, hdat, hIn⟩, hzi⟩ := mem_sep.mp hz
    have hjk' : j < fd.ctors.length := (List.getElem?_eq_some_iff.mp hcj).1
    have hjk : j < a.constructors.length := by
      have := hjk'; rwa [famDataOf_ctors_length] at this
    have hfo : ctorFieldsOf fd j = (a.constructorViews ⟨j, hjk⟩).fields :=
      ctorFieldsOf_famDataOf a ⟨j, hjk⟩
    have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields,
        (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
      have := famDataOf_ctor a ⟨j, hjk⟩
      rw [hcj] at this
      exact Option.some.inj this
    have hcmem : c ∈ fd.ctors := List.getElem?_mem hcj
    have hxs : xs.length = c.1.length :=
      (Sem.InPhi.length _ _ _ _ _ hIn).trans (List.length_map _ _)
    have hD : dataVal j xs ∈ DStar P μ fd σ ρp := by
      have h1 : dataVal j xs ∈ PsiF P μ fd σ ρp Z :=
        mem_sep.mpr ⟨i, ⟨j, c, xs, hcj, hdat, hIn⟩, hdat⟩
      exact mem_congr_right (DStar_fixed P μ fd hN σ ρp hType)
        (PsiF_mono P μ fd σ ρp hZD _ h1)
    obtain ⟨i', hFi⟩ := hD
    have hpD : p (dataVal j xs) := by
      intro idxv hl hfit hre
      have hclsc : FieldsClass fd.fref a.family.member.arity fd.params.length
          fd.indices.length c.1 0 := by
        rw [hcc]
        exact G.fields ⟨j, hjk⟩
      have hInD : Sem.InPhi (semF P μ fd σ ρp c.1) (DStar P μ fd σ ρp)
          (kindsOf fd.fref c.1) xs 0 [] :=
        Sem.InPhi.mono _ hZD (kindsOf fd.fref c.1) xs 0 [] hIn
      have hTT : TelFitsT (mkM P (upd μ fd.fref (famOfD P μ fd (DStar P μ fd))))
          W4 (evalTotal σ fd.resLevel) σ c.1 ρp xs :=
        (telFitsT_iff_InPhi P μ fd a.family.member.arity (DStar P μ fd) hB hpf
          (fun σ' ρ1 ρ' hρ => DStar_env P μ fd hN σ' hρ)
          (fun σ' σ'' hσ ρ1 => DStar_levels P μ fd a.family.member.arity hN hB hσ ρ1)
          (fun σ' ρ1 w hw => DStar_ne P μ fd hN σ' ρ1 w hw)
          (fun σ' ρ1 => DStar_mem P μ fd hN σ' ρ1)
          σ ps hpsl c.1 (fieldsClassA_of_fieldsClass hclsc) xs).mpr hInD
      have hT0 : TelFits (mkM P (upd μ fd.fref (famOfD P μ fd (DStar P μ fd))))
          σ c.1 ρp xs := TelFitsT_telFits _ _ _ _ _ _ _ hTT
      have hvs' := evalTotal_agree (σOf_canon σ a.family.member.arity)
        fd.resLevel hB.res
      have hkk : evalTotal (σOf ((canonL a.family.member.arity).map (evalTotal σ)))
          fd.resLevel ≠ 0 := fun h0 => hType (hvs'.symm.trans h0)
      have hX : famKT P μ fd ((canonL a.family.member.arity).map (evalTotal σ)) =
          famLfp P μ fd ((canonL a.family.member.arity).map (evalTotal σ)) := by
        unfold famKT
        rw [if_neg hkk]
      have hcanon : ∀ e, e ∈ c.1 → CanonOcc fd.fref a.family.member.arity e :=
        fun e he => canonOcc_fieldsClassA (fieldsClassA_of_fieldsClass hclsc) e he
      have hTKT : TelFits (mkM P (tabKT P μ fd)) σ c.1 ρp xs := by
        have h := (TelFits_den_iff P (upd μ fd.fref (famKT P μ fd))
          (upd μ fd.fref (famLfp P μ fd)) σ c.1
          (fun e he ρ1 => den_transfer P μ fd.fref a.family.member.arity σ hX hf e
            (hcanon e he) ρ1) ρp xs).mpr hT0
        exact h
      have hTμ : TelFits (mkM P μ) σ c.1 ρp xs :=
        (TelFits_tables_equiv P (tabKT_equiv P μ a hKT) σ c.1 ρp xs).mp hTKT
      have hrd : Equiv (resTupF P μ fd σ ρp (dataVal j xs))
          (ordPair pempty (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) :=
        resTupF_dataVal P μ fd σ ρp hcj hxs Equiv.rfl
      have hLEq : LEq (c.2.map (den (mkM P μ) σ (push xs ρp))) idxv :=
        tup_inj (by rw [List.length_map, hres_of_admitted a c hcmem, hl])
          (ordPair_equiv (hre.symm.trans hrd)).2.symm
      have hcf : CtorFits (mkM P μ) σ fd.ctors ρp idxv j xs :=
        ⟨c, hcj, hTμ, hLEq⟩
      have hih : IHOkF (mkM P μ) σ fd.params.length mo
          (recCore (mkM P μ) fd ms) fd.fref (ctorFieldsOf fd j) ρp xs := by
        rw [hfo]
        have hIn' : Sem.InPhi (semF P μ fd σ ρp
            ((a.constructorViews ⟨j, hjk⟩).fields)) Z
            (kindsOf fd.fref ((a.constructorViews ⟨j, hjk⟩).fields)) xs 0 [] := by
          have h := hIn
          rw [hcc] at h
          exact h
        exact ihOkF_of_InPhi P μ a vs ps mo ms Z hZ hpsl
          ((a.constructorViews ⟨j, hjk⟩).fields) []
          ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
          (G.fields ⟨j, hjk⟩) hIn'
      have hmin := minor_ok_rec a vs G.opq G.shapes
        (famμ_of_KT P μ a hKT G hN hf vs) hctorμ ps mo ms idxv hpsl hl hmo hms
        hfit j xs hcf _ hih
      have hzd : Equiv (ctorV (mkM P μ) σ fd j xs) (dataVal j xs) := by
        unfold ctorV cond
        dsimp only [mkM]
        cases P.dec (evalTotal σ fd.resLevel = 0) with
        | isTrue h0 => exact absurd h0 hType
        | isFalse _ => exact Equiv.rfl
      have hlen' : xs.length = nfOf fd j := by
        unfold nfOf
        rw [hcj]
        exact hxs
      have hrc : Equiv (recCore (mkM P μ) fd ms (dataVal j xs))
          (fapps (ms.getD j pempty)
            (ihArgs fd.fref (recCore (mkM P μ) fd ms) (ctorFieldsOf fd j) xs)) :=
        recCore_data _ _ _ Equiv.rfl hjk' hlen'
          (ihChildL_famDataOf_fieldsClass a G hcf (dataVal j xs))
      exact mem_congr_right (ed_congr (mkM P μ)
        (fapps_congr_args mo (LEq_append (LEq.refl idxv)
          (show LEq [ctorV (mkM P μ) σ fd j xs] [dataVal j xs] from ⟨hzd, trivial⟩))))
        (mem_congr_left hrc.symm hmin)
    have hp : p ((DStar P μ fd σ ρp).Func i') :=
      motive_pred_resp P μ a vs ps mo ms (dataVal j xs) _ hFi.symm hpD
    exact mem_sep.mpr ⟨i', hp, hFi.trans (hdat.symm.trans hzi)⟩
  intro x hx idxv hl hfit hre
  obtain ⟨i, hpi, hxi⟩ := mem_sep.mp (DStar_least P μ fd hN σ ρp hType hsub x hx)
  exact (motive_pred_resp P μ a vs ps mo ms _ x hxi hpi) idxv hl hfit hre

/-- `rec_fields_ok` at the `famKT` table: a recursive-field value at the real
table satisfies the motive, by `DStar_motive`. -/
theorem rec_fields_ok_KT
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4})
    (hl : idx.length = (famDataOf a).indices.length)
    (hidx : ∀ e, e ∈ idx → occursConst (famDataOf a).fref e = false)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
        (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)))) :
    recCore (mkM P μ) (famDataOf a) ms x ∈
      Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x])) := by
  obtain ⟨hd, he⟩ := (ed_recOcc_KT P μ a hKT G hN hf (σOf vs) hType ps ys hpsl idx hl hidx x).mp hx
  have haf : argsFitF P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
        (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)) := by
    cases hdec : P.dec (argsFitF P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
        (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) with
    | isTrue h => exact h
    | isFalse hn =>
        exfalso
        have hs : recTupAt P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
            (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
              (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)) =
            singleton pempty := by unfold recTupAt; rw [cond_neg hn]
        exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs) (push ps ρ0) x
          (he.trans (by rw [← hs]; exact Equiv.rfl))
  have hre : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x)
      (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0)))))) := by
    have hre2 : recTupAt P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)) =
        ordPair pempty (tup ((familyIdx (famDataOf a).params.length
          (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
            (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))).map
          (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))))) := by
      unfold recTupAt; rw [cond_pos haf]
    rw [familyIdx_directRec] at hre2
    have hse : Equiv (recTupAt P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)))
        (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0)))))) := by
      rw [← hre2]; exact Equiv.rfl
    exact he.trans hse
  have hTf : TelFits (mkM P μ) (σOf vs)
      ((famDataOf a).params ++ (famDataOf a).indices) ρ0
      ((policyParameterLocals (famDataOf a).params.length ys.length ++ idx).map
        (den (mkM P μ) (σOf vs) (push ys (push ps ρ0)))) :=
    (argsFitF_directRec P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
      (famDataOf a).fref (canonL a.family.member.arity) _).mp haf
  have hpsl' : ps.length = (famDataOf a).params.length := hpsl
  have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
  rw [← hpsl'] at hTf
  rw [e] at hTf
  obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
  obtain ⟨rfl, rfl⟩ := List.append_inj heq
    (by rw [TelFits.length h1]; exact hpsl')
  exact DStar_motive P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hType x hd
    (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))))
    (by rw [List.length_map]; exact hl) h2 hre

/-- `minor_ok` for a recursive group at the `famKT` table. -/
theorem minor_ok_group_KT
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (is : List PSet.{4}) (hisl : is.length = (famDataOf a).indices.length)
    (hisfit : TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) is)
    (j : Nat) (xs : List PSet.{4})
    (hcf : CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs) :
    fapps (ms.getD j pempty) (ihArgs (famDataOf a).fref (recCore (mkM P μ) (famDataOf a) ms)
        (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs])) := by
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (famDataOf a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < a.constructors.length := by rwa [famDataOf_ctors_length] at hjk'
  have hfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews ⟨j, hjk⟩).fields :=
    ctorFieldsOf_famDataOf a ⟨j, hjk⟩
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  refine minor_ok_rec a vs G.opq G.shapes (famμ_of_KT P μ a hKT G hN hf vs) hctorμ
    ps mo ms is hpsl hisl hmo hms hisfit j xs hcf _ ?_
  rw [hfo]
  exact ihOkF_walk (mkM P μ) (mkM P μ) (σOf vs) a.family.ref a.family.member.arity
    a.family.parameters.length a.family.indices.length mo _ ps
    (fun ys idx x hl hidx hx =>
      rec_fields_ok_KT P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hType ys idx x hl hidx hx)
    _ [] xs (G.fields ⟨j, hjk⟩) hxs

/-- The recursor of a recursive `Type` group is an element of its type, at a
table carrying `famKT`. -/
theorem recVal_mem_rec_KT
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hType : evalTotal (σOf vs) a.family.resultLevel ≠ 0) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  refine recVal_mem_gen rfl a vs (famμ_of_KT P μ a hKT G hN hf vs)
    (fun h0 => absurd h0 hType) (fun h0 => absurd h0 hType)
    (fun ps is j xs hcf => ihChildL_famDataOf_fieldsClass a G hcf (dataVal j xs))
    (recCore (mkM P μ) (famDataOf a)) (fun _ _ _ => rfl) ?_
  intro ps mo ms is _ hpsl hisl hmo hms hisfit j xs hcf
  exact minor_ok_group_KT P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hType is hisl
    hisfit j xs hcf

/-- `InPhi` analogue for the Prop instance: a `TelFitsP` over `Z` whose
predicate is the motive condition gives `IHOkF` for `g = fun _ => ∅`. -/
theorem ihOkF_of_TelFitsP (Z : PSet.{4})
    (hZ : ∀ t, t ∈ Z → ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv t (tup idxv) →
      pempty ∈ Ed (mkM P μ) (fapps mo (idxv ++ [pempty])))
    (hps : ps.length = (famDataOf a).params.length)
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClass (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
        (famDataOf a).indices.length rest done.length →
      TelFitsP P μ (famDataOf a) Z (σOf vs) rest (push pre (push ps ρ0)) xs →
      IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
        (fun _ => pempty) (famDataOf a).fref rest (push pre (push ps ρ0)) xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls hT
      cases xs with
      | nil => trivial
      | cons x xs' => simp only [TelFitsP] at hT
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls hT
      obtain ⟨hdisj, hcls'⟩ := hcls
      have hf : fieldAt Fs done.length = A := by
        rw [hFs]
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      show IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo
        (fun _ => pempty) (famDataOf a).fref (A :: rest')
        (push pre (push ps ρ0)) xs
      cases xs with
      | nil => simp only [TelFitsP] at hT
      | cons x xs' =>
          simp only [TelFitsP] at hT
          obtain ⟨hx, hin⟩ := hT
          rcases hdisj with h0 | hdr
          · refine ⟨fun ho => ?_, ih_step done A rest' pre x xs' hFs hpre hcls' IH hin⟩
            rw [h0] at ho; cases ho
          · obtain ⟨idx, hAe, hlen, hfree⟩ := hdr
            simp only [okP] at hx
            rw [kindOf_directRec ⟨idx, hAe, hlen, hfree⟩] at hx
            obtain ⟨hpe, haf, htz⟩ := hx
            refine ⟨fun _ => ?_, ih_step done A rest' pre x xs' hFs hpre hcls' IH hin⟩
            rw [hAe] at haf htz
            rw [familyIdx_directRec] at htz
            have hTf : TelFits (mkM P μ) (σOf vs)
                ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                ((policyParameterLocals (famDataOf a).params.length done.length ++ idx).map
                  (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)))) :=
              (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                (push pre (push ps ρ0)) (famDataOf a).fref
                (canonL a.family.member.arity) _).mp haf
            have hpsl' : ps.length = (famDataOf a).params.length := hps
            have e := den_recArgs (mkM P μ) (σOf vs) ps pre idx
            rw [hpre] at e
            rw [← hpsl'] at hTf
            rw [e] at hTf
            obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
            obtain ⟨rfl, rfl⟩ := List.append_inj heq
              (by rw [TelFits.length h1]; exact hpsl')
            rw [hAe, ihAt_foldApps (fun _ _ h => Expr.noConfusion h), familyIdx_directRec]
            have hz := hZ (tup (idx.map (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)))))
              htz _ (by rw [List.length_map]; exact hlen) h2 Equiv.rfl
            exact mem_congr_right (ed_congr (mkM P μ)
              (fapps_congr_args mo (LEq_append (LEq.refl (idx.map (den (mkM P μ) (σOf vs)
                (push pre (push ps ρ0)))))
                (show LEq [pempty] [x] from ⟨hpe.symm, trivial⟩)))) hz
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClass (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest' (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          FieldsClass (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
            (famDataOf a).indices.length rest' done'.length →
          TelFitsP P μ (famDataOf a) Z (σOf vs) rest' (push pre (push ps ρ0)) xs →
          IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo (fun _ => pempty)
            (famDataOf a).fref rest' (push pre (push ps ρ0)) xs)
        (hin : TelFitsP P μ (famDataOf a) Z (σOf vs) rest'
          (vcons x (push pre (push ps ρ0))) xs') :
        IHOkF (mkM P μ) (σOf vs) (famDataOf a).params.length mo (fun _ => pempty)
          (famDataOf a).fref rest' (vcons x (push pre (push ps ρ0))) xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x]) (push ps ρ0) :=
        (push_append pre [x] (push ps ρ0)).symm
      have hFs' : Fs = (done ++ [A]) ++ rest' :=
        hFs.trans (List.append_assoc done [A] rest').symm
      have hlen' : (pre ++ [x]).length = (done ++ [A]).length := by
        rw [List.length_append, List.length_append, hpre]
        rfl
      rw [hvey]
      rw [hvey] at hin
      exact IH (done ++ [A]) (pre ++ [x]) xs' hFs' hlen'
        (by rw [List.length_append]; exact hcls') hin

/-- At a zero level, the family's `Prop` instance is the `tv` of `DStarP`
membership — the `hzm` analogue at the `famKT` table. -/
theorem ed_famApp_KTP
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hk0 : evalTotal (σOf vs) (famDataOf a).resLevel = 0)
    (is : List PSet.{4}) (hisl : is.length = (famDataOf a).indices.length)
    (hfit : TelFits (mkM P μ) (σOf vs) ((famDataOf a).params ++ (famDataOf a).indices) ρ0 (ps ++ is)) :
    Equiv (Ed (mkM P μ) (fapps (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs)))) (ps ++ is)))
      (tv (tup is ∈ DStarP P μ (famDataOf a) (σOf vs) (push ps ρ0))) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  let vs' := (policyFamilyLevels a.family).map (evalTotal (σOf vs))
  have hσa : ∀ i, i < a.family.member.arity → σOf vs' i = σOf vs i :=
    σOf_policyFamilyLevels_agree a.family vs
  have hk0' : evalTotal (σOf vs') (famDataOf a).resLevel = 0 :=
    (evalTotal_agree hσa _ hB.res).trans hk0
  have hX : famKT P μ (famDataOf a) vs' = famLfpP P μ (famDataOf a) vs' := by
    unfold famKT
    rw [if_pos hk0']
  have hKT' : Equiv (μ a.family.ref vs') (famLfpP P μ (famDataOf a) vs') :=
    hX.symm ▸ hKT vs'
  have hfit' : TelFits (mkM P μ) (σOf vs') ((famDataOf a).params ++ (famDataOf a).indices)
      ρ0 (ps ++ is) :=
    (TelFits_levels (mkM P μ) hσa _ (hpi_of _ _ hB) ρ0 (ps ++ is)).mpr hfit
  have hfa := fapps_fam_fit P μ (famDataOf a) (σOf vs')
    (famEndP_envResp P μ (famDataOf a) (σOf vs')) (ps ++ is) hfit'
  have hlv := famEndP_levels P μ (famDataOf a) a.family.member.arity hB hσa
    (push (ps ++ is) ρ0)
  have hpush : push (ps ++ is) ρ0 = push is (push ps ρ0) := push_append ps is ρ0
  have hed : Equiv (Ed (mkM P μ) (famEndP P μ (famDataOf a) (σOf vs) (push (ps ++ is) ρ0)))
      (tv (tup is ∈ DStarP P μ (famDataOf a) (σOf vs) (push ps ρ0))) := by
    show Equiv (Ed (mkM P μ) (tyv (tv (tup (lastVals (famDataOf a).indices.length
        (push (ps ++ is) ρ0)) ∈
        DStarP P μ (famDataOf a) (σOf vs) (shiftρ (famDataOf a).indices.length
          (push (ps ++ is) ρ0)))))) _
    rw [hpush, ← hisl, lastVals_push, shiftρ_push]
    exact ed_tyv_of_dich (mkM P μ) (dich_tv _)
  exact (ed_congr (mkM P μ) (fapps_congr hKT' _)).trans
    ((ed_congr (mkM P μ) (hfa.trans hlv)).trans hed)

include G hpsl
/-- At a zero level, the recursor's minor premise (the `tv` of `DStarP`
membership) is inhabited at every derivable instance — `DStarP` induction. -/
theorem DStarP_motive
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hpsfit : TelFits (mkM P μ) (σOf vs) (famDataOf a).params ρ0 ps)
    (hk0 : evalTotal (σOf vs) (famDataOf a).resLevel = 0)
    (hpol : a.policy = .propOnly) :
    ∀ t, t ∈ DStarP P μ (famDataOf a) (σOf vs) (push ps ρ0) →
      ∀ idxv : List PSet.{4}, idxv.length = (famDataOf a).indices.length →
        TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
        Equiv t (tup idxv) →
        pempty ∈ Ed (mkM P μ) (fapps mo (idxv ++ [pempty])) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  have hpf : ∀ e, e ∈ (famDataOf a).params ++ (famDataOf a).indices →
      occursConst (famDataOf a).fref e = false := G.famFree
  let σ := σOf vs
  let fd := famDataOf a
  let ρp := push ps ρ0
  let p : PSet.{4} → Prop := fun t => ∀ idxv : List PSet.{4},
    idxv.length = (famDataOf a).indices.length →
    TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
    Equiv t (tup idxv) →
    pempty ∈ Ed (mkM P μ) (fapps mo (idxv ++ [pempty]))
  let Z := sep p (DStarP P μ fd σ ρp)
  have hZD : Sub Z (DStarP P μ fd σ ρp) := fun w hw => mem_sep_subset hw
  have hZ : ∀ t, t ∈ Z → ∀ idxv : List PSet.{4},
      idxv.length = (famDataOf a).indices.length →
      TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) idxv →
      Equiv t (tup idxv) →
      pempty ∈ Ed (mkM P μ) (fapps mo (idxv ++ [pempty])) :=
    fun t ht idxv hl hfit hre => by
      obtain ⟨i, hpi, hti⟩ := mem_sep.mp ht
      exact hpi idxv hl hfit (hti.trans hre)
  have hsub : Sub (PhiP P μ fd σ ρp Z) Z := by
    intro t ht
    obtain ⟨i, ⟨j, c, xs, hcj, hT, hdat⟩, htz⟩ := mem_sep.mp ht
    have hjk' : j < fd.ctors.length := (List.getElem?_eq_some_iff.mp hcj).1
    have hjk : j < a.constructors.length := by
      have := hjk'; rwa [famDataOf_ctors_length] at this
    have hfo : ctorFieldsOf fd j = (a.constructorViews ⟨j, hjk⟩).fields :=
      ctorFieldsOf_famDataOf a ⟨j, hjk⟩
    have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields,
        (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
      have := famDataOf_ctor a ⟨j, hjk⟩
      rw [hcj] at this
      exact Option.some.inj this
    have hcmem : c ∈ fd.ctors := List.getElem?_mem hcj
    have hD : (UP P μ fd σ ρp).Func i ∈ DStarP P μ fd σ ρp :=
      (DStarP_isLfp P μ fd σ ρp).1 _
        (PhiP_mono P μ fd σ ρp hZD _
          (mem_sep.mpr ⟨i, ⟨j, c, xs, hcj, hT, hdat⟩, Equiv.refl _⟩))
    obtain ⟨i', hFi⟩ := hD
    have hpD : p ((UP P μ fd σ ρp).Func i) := by
      intro idxv hl hfit hre
      have hze : Equiv (tup (c.2.map (den (mkM P μ) σ (push xs ρp)))) (tup idxv) :=
        hdat.symm.trans hre
      have hLEq : LEq (c.2.map (den (mkM P μ) σ (push xs ρp))) idxv :=
        tup_inj (by rw [List.length_map, hres_of_admitted a c hcmem, hl]) hze
      have hTD : TelFitsP P μ fd (DStarP P μ fd σ ρp) σ c.1 ρp xs :=
        TelFitsP_mono P μ fd hZD σ c.1 ρp xs hT
      have hclsc : FieldsClass fd.fref a.family.member.arity fd.params.length
          fd.indices.length c.1 0 := by
        rw [hcc]
        exact G.fields ⟨j, hjk⟩
      have hT0 : TelFits (mkM P (upd μ fd.fref (famLfpP P μ fd))) σ c.1 ρp xs :=
        (telFits_iff_TelFitsP P μ fd a.family.member.arity hB hpf σ ps hpsl
          (fieldsClassA_of_fieldsClass hclsc) xs).mpr hTD
      have hvs' := evalTotal_agree (σOf_policyFamilyLevels_agree a.family vs)
        fd.resLevel hB.res
      have hkk : evalTotal (σOf ((policyFamilyLevels a.family).map (evalTotal σ)))
          fd.resLevel = 0 := hvs'.trans hk0
      have hX : famKT P μ fd ((policyFamilyLevels a.family).map (evalTotal σ)) =
          famLfpP P μ fd ((policyFamilyLevels a.family).map (evalTotal σ)) := by
        unfold famKT
        rw [if_pos hkk]
      have hcanon : ∀ e, e ∈ c.1 → CanonOcc fd.fref a.family.member.arity e :=
        fun e he => canonOcc_fieldsClassA (fieldsClassA_of_fieldsClass hclsc) e he
      have hTKT : TelFits (mkM P (tabKT P μ fd)) σ c.1 ρp xs := by
        exact (TelFits_den_iff P (upd μ fd.fref (famKT P μ fd))
          (upd μ fd.fref (famLfpP P μ fd)) σ c.1
          (fun e he ρ1 => den_transfer P μ fd.fref a.family.member.arity σ hX hf e
            (hcanon e he) ρ1) ρp xs).mpr hT0
      have hTμ : TelFits (mkM P μ) σ c.1 ρp xs :=
        (TelFits_tables_equiv P (tabKT_equiv P μ a hKT) σ c.1 ρp xs).mp hTKT
      have hcf : CtorFits (mkM P μ) σ fd.ctors ρp idxv j xs :=
        ⟨c, hcj, hTμ, hLEq⟩
      have hih : IHOkF (mkM P μ) σ fd.params.length mo (fun _ => pempty)
          fd.fref (ctorFieldsOf fd j) ρp xs := by
        rw [hfo]
        have hT' : TelFitsP P μ fd Z σ ((a.constructorViews ⟨j, hjk⟩).fields) ρp xs := by
          have h := hT
          rw [hcc] at h
          exact h
        exact ihOkF_of_TelFitsP P μ a G vs ps mo hpsl Z hZ hpsl
          ((a.constructorViews ⟨j, hjk⟩).fields) []
          ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
          (G.fields ⟨j, hjk⟩) hT'
      have hmin := minor_ok_rec a vs G.opq G.shapes
        (famμ_of_KT P μ a hKT G hN hf vs) hctorμ ps mo ms idxv hpsl hl hmo hms
        hfit j xs hcf _ hih
      have hcv : Equiv (ctorV (mkM P μ) σ fd j xs) pempty := by
        unfold ctorV cond
        dsimp only [mkM]
        cases P.dec (evalTotal σ fd.resLevel = 0) with
        | isTrue _ => exact Equiv.rfl
        | isFalse h => exact absurd hk0 h
      have hzm : ctorV (mkM P μ) σ fd j xs ∈ Ed (mkM P μ)
          (fapps (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal σ)))
            (ps ++ idxv)) := by
        have hfit' : TelFits (mkM P μ) σ ((famDataOf a).params ++ (famDataOf a).indices)
            ρ0 (ps ++ idxv) := TelFits.append hpsfit hfit
        have hmem : tup idxv ∈ DStarP P μ fd σ ρp :=
          mem_congr_left (hdat.trans hze) ⟨i', hFi⟩
        exact mem_congr_left hcv.symm
          (mem_congr_right (ed_famApp_KTP P μ a G vs ps hpsl hf hKT hk0 idxv hl hfit').symm
            (mem_tv.mpr ⟨hmem, Equiv.refl _⟩))
      have hym : pempty ∈ Ed (mkM P μ) (fapps mo (idxv ++ [ctorV (mkM P μ) σ fd j xs])) :=
        mem_congr_left (motive_prop_elem rfl a vs ps mo idxv (ctorV (mkM P μ) σ fd j xs)
          hpsl hl hpol hmo hfit hzm _ hmin) hmin
      exact mem_congr_right (ed_congr (mkM P μ)
        (fapps_congr_args mo (LEq_append (LEq.refl idxv)
          (show LEq [ctorV (mkM P μ) σ fd j xs] [pempty] from ⟨hcv, trivial⟩)))) hym
    exact mem_sep.mpr ⟨i', fun idxv hl hfit hre => hpD idxv hl hfit (hFi.symm.trans hre),
      hFi.trans htz⟩
  intro t ht idxv hl hfit hre
  obtain ⟨i, hpi, hti⟩ := mem_sep.mp ((DStarP_isLfp P μ fd σ ρp).2.2 Z hsub t ht)
  exact hpi idxv hl hfit (hti.trans hre)


/-- `rec_fields_ok` at the `famKT` table for a zero result level: a recursive
field value is `∅` and the motive at `∅` is inhabited, by `DStarP_motive`. -/
theorem rec_fields_ok_KTP
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hpsfit : TelFits (mkM P μ) (σOf vs) (famDataOf a).params ρ0 ps)
    (hk0 : evalTotal (σOf vs) (famDataOf a).resLevel = 0)
    (hpol : a.policy = .propOnly)
    (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4})
    (hl : idx.length = (famDataOf a).indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst (famDataOf a).fref e = false)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
        (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)))) :
    pempty ∈ Ed (mkM P μ) (fapps mo
      (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x])) := by
  obtain ⟨hpe, haf, htz⟩ := (ed_recOcc_KTP P μ a hKT G hN hf (σOf vs) hk0 ps ys hpsl
    idx hl hfree x).mp hx
  have hTf : TelFits (mkM P μ) (σOf vs)
      ((famDataOf a).params ++ (famDataOf a).indices) ρ0
      ((policyParameterLocals (famDataOf a).params.length ys.length ++ idx).map
        (den (mkM P μ) (σOf vs) (push ys (push ps ρ0)))) :=
    (argsFitF_directRec P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
      (famDataOf a).fref (canonL a.family.member.arity) _).mp haf
  have hpsl' : ps.length = (famDataOf a).params.length := hpsl
  have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
  rw [← hpsl'] at hTf
  rw [e] at hTf
  obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
  obtain ⟨rfl, rfl⟩ := List.append_inj heq
    (by rw [TelFits.length h1]; exact hpsl')
  have hm := DStarP_motive P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hpsfit
    hk0 hpol _ htz _ (by rw [List.length_map]; exact hl) h2 (Equiv.refl _)
  exact mem_congr_right (ed_congr (mkM P μ)
    (fapps_congr_args mo (LEq_append (LEq.refl (idx.map (den (mkM P μ) (σOf vs)
      (push ys (push ps ρ0)))))
      (show LEq [pempty] [x] from ⟨hpe.symm, trivial⟩)))) hm

/-- `minor_ok` for a recursive Prop group at the `famKT` table. -/
theorem minor_ok_group_KTP
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hpsfit : TelFits (mkM P μ) (σOf vs) (famDataOf a).params ρ0 ps)
    (hk0 : evalTotal (σOf vs) (famDataOf a).resLevel = 0)
    (hpol : a.policy = .propOnly)
    (is : List PSet.{4}) (hisl : is.length = (famDataOf a).indices.length)
    (hisfit : TelFits (mkM P μ) (σOf vs) (famDataOf a).indices (push ps ρ0) is)
    (j : Nat) (xs : List PSet.{4})
    (hcf : CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs) :
    fapps (ms.getD j pempty) (ihArgs (famDataOf a).fref (fun _ => pempty)
        (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs])) := by
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (famDataOf a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < a.constructors.length := by rwa [famDataOf_ctors_length] at hjk'
  have hfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews ⟨j, hjk⟩).fields :=
    ctorFieldsOf_famDataOf a ⟨j, hjk⟩
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  refine minor_ok_rec a vs G.opq G.shapes (famμ_of_KT P μ a hKT G hN hf vs) hctorμ
    ps mo ms is hpsl hisl hmo hms hisfit j xs hcf _ ?_
  rw [hfo]
  exact ihOkF_walk (mkM P μ) (mkM P μ) (σOf vs) a.family.ref a.family.member.arity
    a.family.parameters.length a.family.indices.length mo (fun _ => pempty) ps
    (fun ys idx x hl hidx hx =>
      rec_fields_ok_KTP P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hpsfit
        hk0 hpol ys idx x hl hidx hx)
    _ [] xs (G.fields ⟨j, hjk⟩) hxs

/-- The recursor of a recursive `Prop` group eliminating into `Prop` is an
element of its type, at the `famKT` table. -/
theorem recVal_mem_recP_KT
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hProp : evalTotal (σOf vs) a.family.resultLevel = 0)
    (hpol : a.policy = .propOnly) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  have hProp' : evalTotal (σOf vs) (famDataOf a).resLevel = 0 := hProp
  refine recVal_mem_gen rfl a vs (famμ_of_KT P μ a hKT G hN hf vs)
    (fun _ hp => by rw [hpol] at hp; cases hp)
    (fun _ hp => by rw [hpol] at hp; cases hp)
    (fun ps is j xs hcf => ihChildL_famDataOf_fieldsClass a G hcf (dataVal j xs))
    (fun _ _ => pempty) (fun h0 => absurd hProp' h0) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  exact minor_ok_group_KTP P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo hms hps
    hProp' hpol is hisl hisfit j xs hcf

end

end Rcic.F3.PSet
