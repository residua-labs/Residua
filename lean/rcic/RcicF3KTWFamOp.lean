import rcic.RcicF3KTWFamField
import rcic.RcicF3DTransfer

/-!
# F3 S7 KT-2b-3c-3c: the family operator and its fixed-point equation

`PsiF P μ fd σ ρp X` collects the constructor data whose fields satisfy the
`semF` guards at `X`; `PhiF` composes it with a data-set function `D`.  The main
equation `famVal(famOfD D) ≈ famOfD (PhiF D)` is the F3 class-A fixed point.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

/-- `piLam` congruence across two interps sharing `dec`, at fitting values. -/
theorem piLam_congr_fits₂ (M₁ M₂ : Interp.{T}) (hdec : M₁.dec = M₂.dec)
    (σ : Nat → Nat) {g g' : (Nat → PSet.{T}) → PSet.{T}}
    (hg : EnvResp g) (hg' : EnvResp g')
    (b : Expr Nat) (hb : ∀ A B, b ≠ .pi A B) :
    (Ds : List (Expr Nat)) → (ρ : Nat → PSet.{T}) →
    (∀ ρ' A, A ∈ Ds → den M₁ σ ρ' A = den M₂ σ ρ' A) →
    (∀ xs, TelFits M₁ σ Ds ρ xs → Equiv (g (push xs ρ)) (g' (push xs ρ))) →
    Equiv (piLam M₁ σ g ρ (policyPi Ds b)) (piLam M₂ σ g' ρ (policyPi Ds b))
  | [], ρ, hden, h => by
      cases b with
      | pi A B => exact absurd rfl (hb A B)
      | _ => exact h [] trivial
  | A :: Ds, ρ, hden, h => by
      have hdenA : den M₁ σ ρ A = den M₂ σ ρ A := hden ρ A (List.mem_cons_self _ _)
      have hEd : Ed M₁ (den M₂ σ ρ A) = Ed M₂ (den M₂ σ ρ A) := by
        unfold Ed; rw [hdec]
      show Equiv (lamVal M₁ (den M₁ σ ρ A) (fun x => piLam M₁ σ g (vcons x ρ) (policyPi Ds b)))
          (lamVal M₂ (den M₂ σ ρ A) (fun x => piLam M₂ σ g' (vcons x ρ) (policyPi Ds b)))
      rw [hdenA]
      unfold lamVal
      rw [hdec]
      refine cond_congr
        ⟨fun hl x hx => ?_, fun hl x hx => ?_⟩ Equiv.rfl (mkLam_congr_on
          (fun x x' hx => piLam_congr M₁ σ hg (policyPi Ds b)
            (vcons_congr hx (fun _ => Equiv.rfl)))
          (by rw [hEd]; exact Equiv.rfl)
          (fun x hx => ?_))
      · have hx1 : x ∈ Ed M₁ (den M₁ σ ρ A) := by
          have hx' := hEd.symm ▸ hx
          rwa [← hdenA] at hx'
        exact (piLam_congr_fits₂ M₁ M₂ hdec σ hg hg' b hb Ds (vcons x ρ)
          (fun ρ' A' hA' => hden ρ' A' (List.mem_cons_of_mem _ hA'))
          (fun xs hT => h (x :: xs) ⟨hx1, hT⟩)).symm.trans (hl x (hEd.symm ▸ hx))
      · have hx1 : x ∈ Ed M₁ (den M₁ σ ρ A) := by
          rwa [← hdenA] at hx
        exact (piLam_congr_fits₂ M₁ M₂ hdec σ hg hg' b hb Ds (vcons x ρ)
          (fun ρ' A' hA' => hden ρ' A' (List.mem_cons_of_mem _ hA'))
          (fun xs hT => h (x :: xs) ⟨hx1, hT⟩)).trans (hl x (hEd ▸ hx))
      · have hx1 : x ∈ Ed M₁ (den M₁ σ ρ A) := by
          rwa [← hdenA] at hx
        exact piLam_congr_fits₂ M₁ M₂ hdec σ hg hg' b hb Ds (vcons x ρ)
          (fun ρ' A' hA' => hden ρ' A' (List.mem_cons_of_mem _ hA'))
          (fun xs hT => h (x :: xs) ⟨hx1, hT⟩)

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
  (hD2 : ∀ σ σ', (∀ i, i < ar → σ i = σ' i) → ∀ ρ, Equiv (D σ ρ) (D σ' ρ))
  (hD3 : ∀ σ ρ z, z ∈ D σ ρ → ¬ Equiv z pempty)
  (hD4 : ∀ σ ρ, D σ ρ ∈ W4 (evalTotal σ fd.resLevel))
  (hclsA : ∀ c, c ∈ fd.ctors →
    FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
  (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
  (hres : ∀ c, c ∈ fd.ctors → c.2.length = fd.indices.length)

/-- The family operator: data whose fields satisfy the `semF` guards at `X`. -/
def PsiF (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (X : PSet.{4}) : PSet.{4} :=
  sep (fun z => ∃ j c xs, fd.ctors[j]? = some c ∧ Equiv z (dataVal j xs) ∧
      Sem.InPhi (semF P μ fd σ ρp c.1) X (kindsOf fd.fref c.1) xs 0 [])
    (W4 (evalTotal σ fd.resLevel))

/-- `PsiF` composed with a data-set function. -/
def PhiF (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4}) :
    (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4} :=
  fun σ ρp => PsiF P μ fd σ ρp (D σ ρp)

/-- `PsiF` is monotone in the candidate set. -/
theorem PsiF_mono (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {X Y : PSet.{4}}
    (h : Sub X Y) : Sub (PsiF P μ fd σ ρp X) (PsiF P μ fd σ ρp Y) := by
  intro z hz
  obtain ⟨i, ⟨j, c, xs, hcj, hiz, hIn⟩, hi⟩ := mem_sep.mp hz
  exact mem_sep.mpr ⟨i, ⟨j, c, xs, hcj, hiz,
    Sem.InPhi.mono _ h (kindsOf fd.fref c.1) xs 0 [] hIn⟩, hi⟩

/-- `resTupF` of a data value is the ordPair of its evaluated index tuple. -/
theorem resTupF_dataVal (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {j : Nat}
    {c : List (Expr Nat) × List (Expr Nat)} {xs : List PSet.{4}}
    (hj : fd.ctors[j]? = some c) (hl : xs.length = c.1.length) {z : PSet.{4}}
    (hz : Equiv z (dataVal j xs)) :
    Equiv (resTupF P μ fd σ ρp z)
      (ordPair pempty (tup (c.2.map (den (mkM P μ) σ (push xs ρp))))) := by
  refine (resTupF_congr P μ fd σ ρp hz).trans ?_
  have hlt : j < fd.ctors.length := (List.getElem?_eq_some.mp hj).1
  have hfind : findIdx (mkM P μ) (fun j' => Equiv (tagOf (dataVal j xs)) (ord j'))
      fd.ctors.length = some j :=
    findIdx_eq (mkM P μ) _ (tagOf_dataVal j xs)
      (fun i hi => ((tagOf_dataVal j xs).symm.trans hi |> ord_inj).symm) fd.ctors.length hlt
  have hc : fd.ctors.getD j ([], []) = c := by
    rw [List.getD_eq_getElem?_getD, hj, Option.getD_some]
  have hnf : nfOf fd j = xs.length := by
    rw [nfOf_eq, ctorFieldsOf, hc]; exact hl.symm
  unfold resTupF
  rw [hfind]
  show Equiv (ordPair pempty (tup ((fd.ctors.getD j ([], [])).2.map
      (den (mkM P μ) σ (push (untup (nfOf fd j) (payload (dataVal j xs))) ρp))))) _
  rw [hc]
  exact ordPair_congr Equiv.rfl (tup_congr (LEq_map_den (mkM P μ) σ
    (push_congr (LEq.trans (untup_congr' (nfOf fd j) (payload_dataVal j xs))
      (hnf ▸ untup_tup xs)) (fun _ => Equiv.rfl)) c.2))

/-- `nonrecOkF` respects `≈` in the parameter environment. -/
theorem nonrecOkF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) (x : PSet.{4}) :
    nonrecOkF P μ fd σ ρp Fs k pre x ↔ nonrecOkF P μ fd σ ρp' Fs k pre x :=
  ⟨fun hx => mem_congr_right (truncW_congr (mkM P μ) W4 _
      (ed_congr (mkM P μ) (den_congr (mkM P μ) σ _ (push_congr (LEq.refl pre) h)))) hx,
   fun hx => mem_congr_right (truncW_congr (mkM P μ) W4 _
      (ed_congr (mkM P μ) (den_congr (mkM P μ) σ _ (push_congr (LEq.refl pre) h)))).symm hx⟩

/-- `domEF` respects `≈` in the parameter environment. -/
theorem domEF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) :
    Equiv (domEF P μ σ ρp Fs k pre) (domEF P μ σ ρp' Fs k pre) :=
  ed_congr (mkM P μ) (den_congr (mkM P μ) σ _ (push_congr (LEq.refl pre) h))

/-- `domBigF` respects `≈` in the parameter environment. -/
theorem domBigF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) :
    Equiv (domBigF P μ fd σ ρp Fs k pre) (domBigF P μ fd σ ρp' Fs k pre) := by
  unfold domBigF
  split
  · exact cond_congr ⟨fun hm => mem_congr_left (domEF_env P μ σ h Fs k pre) hm,
      fun hm => mem_congr_left (domEF_env P μ σ h Fs k pre).symm hm⟩
      (domEF_env P μ σ h Fs k pre) Equiv.rfl
  · exact Equiv.rfl

/-- `recTupF` respects `≈` in the parameter environment. -/
theorem recTupF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) (y : PSet.{4}) :
    Equiv (recTupF P μ fd σ ρp Fs k pre y) (recTupF P μ fd σ ρp' Fs k pre y) := by
  unfold recTupF
  split
  · exact cond_congr ⟨fun hm => mem_congr_left (domEF_env P μ σ h Fs k pre) hm,
      fun hm => mem_congr_left (domEF_env P μ σ h Fs k pre).symm hm⟩
      (recTupAt_congr P μ fd σ (vcons_congr Equiv.rfl (push_congr (LEq.refl pre) h))
        (piCod (fieldAt Fs k))) Equiv.rfl
  · exact recTupAt_congr P μ fd σ (push_congr (LEq.refl pre) h) (fieldAt Fs k)

/-- `Sem.InPhi` at `semF` respects `≈` in the parameter environment and in `X`. -/
theorem InPhi_semF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    (Fs : List (Expr Nat)) {X X' : PSet.{4}} (hX : Equiv X X') :
    ∀ (ps : List PKind) (xs : List PSet.{4}) (k : Nat) (pre : List PSet.{4}),
      Sem.InPhi (semF P μ fd σ ρp Fs) X ps xs k pre →
      Sem.InPhi (semF P μ fd σ ρp' Fs) X' ps xs k pre
  | [], xs, _, _, hIn => by
      cases xs with
      | nil => exact hIn
      | cons x xs' => exact hIn
  | .plain :: ps, x :: xs, k, pre, ⟨hx, hin⟩ =>
      ⟨(nonrecOkF_env P μ fd σ h Fs k pre x).1 hx,
        InPhi_semF_env σ h Fs hX ps xs (k + 1) (pre ++ [x]) hin⟩
  | .direct :: ps, x :: xs, k, pre, ⟨⟨hxm, hxe⟩, hin⟩ =>
      ⟨⟨mem_congr_right hX hxm,
        ((resTupF_env P μ fd σ h x).symm.trans hxe).trans
          (recTupF_env P μ fd σ h Fs k pre pempty)⟩,
        InPhi_semF_env σ h Fs hX ps xs (k + 1) (pre ++ [x]) hin⟩
  | .fn :: ps, x :: xs, k, pre, ⟨hxm, hin⟩ =>
      ⟨mem_piSet_of_dep (fun y y' hy => Sem.fib_resp (semF P μ fd σ ρp' Fs) X' k pre hy)
        (isFuncOnDep_equiv (domBigF_env P μ fd σ h Fs k pre)
          (fun y y' hy => sep_congr
            (fun a b hab hb =>
              ((resTupF_env P μ fd σ h b).symm.trans
                ((resTupF_congr P μ fd σ ρp hab.symm).trans hb)).trans
                ((recTupF_env P μ fd σ h Fs k pre y).trans
                  (recTupF_congr P μ fd σ ρp' Fs k (LEq.refl pre) hy)))
            (fun a b hab hb =>
              ((resTupF_env P μ fd σ (fun i => (h i).symm) b).symm.trans
                ((resTupF_congr P μ fd σ ρp' hab.symm).trans hb)).trans
                ((recTupF_env P μ fd σ (fun i => (h i).symm) Fs k pre y').trans
                  (recTupF_congr P μ fd σ ρp Fs k (LEq.refl pre) hy.symm)))
            hX)
          (Equiv.refl x)
          (isFuncOnDep_of_mem_piSet
            (fun y y' hy => Sem.fib_resp (semF P μ fd σ ρp Fs) X k pre hy) hxm)),
        InPhi_semF_env σ h Fs hX ps xs (k + 1) (pre ++ [x]) hin⟩
  | p :: ps, [], _, _, hIn => by cases p <;> exact hIn

/-- `PsiF` respects `≈` in the parameter environment and in the candidate set. -/
theorem PsiF_env (σ : Nat → Nat) {ρp ρp' : Nat → PSet.{4}} (h : ∀ i, Equiv (ρp i) (ρp' i))
    {X X' : PSet.{4}} (hX : Equiv X X') :
    Equiv (PsiF P μ fd σ ρp X) (PsiF P μ fd σ ρp' X') := by
  unfold PsiF
  exact sep_congr
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_env P μ fd σ h c.1 hX (kindsOf fd.fref c.1) xs 0 [] hIn⟩)
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_env P μ fd σ (fun i => (h i).symm) c.1 hX.symm
        (kindsOf fd.fref c.1) xs 0 [] hIn⟩)
    Equiv.rfl

include hB hpf hD1 hD2 hD3 hD4 hclsA hri hres
/-- The constructor fibre at `famOfD D` is the `fibAt` of `PhiF D`. -/
theorem TypeFib_famOfD (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) (is : List PSet.{4})
    (his : is.length = fd.indices.length) :
    Equiv (TypeFib (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4
        (evalTotal σ fd.resLevel) σ fd.ctors (push ps ρ0) is)
      (fibAt P μ fd (PhiF P μ fd D) σ (push ps ρ0) is) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨j, c, xs, hcj, hIn, hL, hze⟩ := (mem_TypeFib_famOfD P μ fd ar D hB hpf hD1
      hD2 hD3 hD4 σ ps hps hclsA hri is z).mp hz
    have hzW : z ∈ W4 (evalTotal σ fd.resLevel) :=
      (stageW4 P _).trans (TypeFib_mem (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ
        (stageW4 P _) fd.ctors (push ps ρ0) is) hz
    obtain ⟨i, hiz⟩ := hzW
    have hlen : xs.length = c.1.length :=
      (Sem.InPhi.length _ (kindsOf fd.fref c.1) xs 0 [] hIn).trans (List.length_map _ _)
    have hzd : Equiv ((W4 (evalTotal σ fd.resLevel)).Func i) (dataVal j xs) :=
      hiz.trans hze
    have hmem : z ∈ PsiF P μ fd σ (push ps ρ0) (D σ (push ps ρ0)) :=
      mem_sep.mpr ⟨i, ⟨j, c, xs, hcj, hzd, hIn⟩, hiz⟩
    obtain ⟨i', hp', hi'⟩ := mem_sep.mp hmem
    refine mem_sep.mpr ⟨⟨i', hp'⟩, ?_, hi'⟩
    exact (resTupF_congr P μ fd σ (push ps ρ0) hi').trans
      ((resTupF_dataVal P μ fd σ (push ps ρ0) hcj hlen hze).trans
        (ordPair_congr Equiv.rfl (tup_congr hL)))
  · intro hz
    obtain ⟨i, hpred, hiz⟩ := mem_sep.mp hz
    obtain ⟨i', ⟨j, c, xs, hcj, hic, hIn⟩, hiz'⟩ := mem_sep.mp (⟨i, hiz⟩ : z ∈ PsiF P μ fd σ (push ps ρ0) (D σ (push ps ρ0)))
    have hze : Equiv z (dataVal j xs) := hiz'.symm.trans hic
    have hlen : xs.length = c.1.length :=
      (Sem.InPhi.length _ (kindsOf fd.fref c.1) xs 0 [] hIn).trans (List.length_map _ _)
    have hc : c ∈ fd.ctors := List.getElem?_mem hcj
    have e1 := resTupF_dataVal P μ fd σ (push ps ρ0) hcj hlen hze
    have e2 := (resTupF_congr P μ fd σ (push ps ρ0) hiz).trans e1
    have hte := (ordPair_equiv (e2.symm.trans hpred)).2
    have hL : LEq (c.2.map (den (mkM P μ) σ (push xs (push ps ρ0)))) is :=
      tup_inj (by rw [List.length_map, hres c hc, his]) hte
    exact (mem_TypeFib_famOfD P μ fd ar D hB hpf hD1 hD2 hD3 hD4
      σ ps hps hclsA hri is z).mpr ⟨j, c, xs, hcj, hIn, hL, hze⟩



/-- `PhiF` respects `≈` in the parameter environment. -/
theorem PhiF_env (σ : Nat → Nat) (ρ ρ' : Nat → PSet.{4})
    (hρ : ∀ i, Equiv (ρ i) (ρ' i)) :
    Equiv (PhiF P μ fd D σ ρ) (PhiF P μ fd D σ ρ') :=
  PsiF_env P μ fd σ hρ (hD1 σ ρ ρ' hρ)

/-- `famVal` at the `famOfD`-table equals `famOfD (PhiF D)` — the fixed point. -/
theorem famVal_famOfD (vs : List Nat) (hk : evalTotal (σOf vs) fd.resLevel ≠ 0) :
    Equiv (famVal (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (σOf vs) fd)
      (famOfD P μ fd (PhiF P μ fd D) vs) := by
  let σ := σOf vs
  show Equiv (piLam (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ
      (famEnd _ W4 σ fd) (fun _ => pempty) (famType fd))
    (piLam (mkM P μ) σ (famEndD P μ fd (PhiF P μ fd D) σ) ρ0 (famType fd))
  unfold famType
  refine piLam_congr_fits₂ (mkM P (upd μ fd.fref (famOfD P μ fd D))) (mkM P μ) rfl σ
    (famEnd_resp _ W4 σ fd)
    (famEndD_envResp P μ fd (PhiF P μ fd D) (PhiF_env P μ fd ar D hB hpf hD1 hD2 hD3 hD4 hclsA hri hres) σ)
    (.sort fd.resLevel) (fun A B e => Expr.noConfusion e)
    (fd.params ++ fd.indices) (fun _ => pempty)
    (fun ρ' A hA => den_off P μ fd.fref (famOfD P μ fd D) σ ρ' (hpf A hA))
    (fun xs hT => ?_)
  obtain ⟨ps', is', hxs, hT1, hT2⟩ :=
    TelFits_split fd.params fd.indices (fun _ => pempty) xs hT
  subst hxs
  have hps' : ps'.length = fd.params.length := TelFits.length hT1
  have his' : is'.length = fd.indices.length := TelFits.length hT2
  show Equiv (famEnd (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 σ fd
      (push (ps' ++ is') ρ0))
    (famEndD P μ fd (PhiF P μ fd D) σ (push (ps' ++ is') ρ0))
  rw [push_append]
  unfold famEnd famEndD
  rw [cond_neg hk, ← his', shiftρ_push, lastVals_push]
  exact tyv_congr (TypeFib_famOfD P μ fd ar D hB hpf hD1 hD2 hD3 hD4 hclsA hri hres
    σ ps' hps' is' his')

end

end PSet

end Rcic.F3
