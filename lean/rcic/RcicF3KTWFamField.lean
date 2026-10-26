import rcic.RcicF3KTWFamDict

/-!
# F3 S7 KT-2b-3c-3b-2a: field-level dictionary

The set a field denotes at the table carrying `famOfD D`, read as the `semF`
guards: plain fields (L3), recursive occurrences (L0), direct fields (L1), and
function-recursive fields (L2).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData) (ar : Nat)
  (D : (Nat → Nat) → (Nat → PSet.{4}) → PSet.{4})
  (hB : FamBounded fd ar)
  (hpf : ∀ e, e ∈ fd.params ++ fd.indices → occursConst fd.fref e = false)
  (hD1 : ∀ σ ρ ρ', (∀ i, Equiv (ρ i) (ρ' i)) → Equiv (D σ ρ) (D σ ρ'))
  (hD2 : ∀ σ σ', (∀ i, i < ar → σ i = σ' i) → ∀ ρ, Equiv (D σ ρ) (D σ' ρ))
  (hD3 : ∀ σ ρ z, z ∈ D σ ρ → ¬ Equiv z pempty)
  (hD4 : ∀ σ ρ, D σ ρ ∈ W4 (evalTotal σ fd.resLevel))

/-- `truncW` is the identity on sets already in the stage. -/
theorem truncW_of_mem {M : Interp.{T}} {W : Nat → PSet.{T}} {k : Nat} {S : PSet.{T}}
    (h : S ∈ W k) : truncW M W k S = S := by
  unfold truncW
  exact cond_pos h S pempty

/-- L3: a family-free field denotes the `nonrecOkF` guard, truncated. -/
theorem truncW_plain_field (σ : Nat → Nat) (ps pre : List PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (A : Expr Nat) (x : PSet.{4})
    (hA : occursConst fd.fref A = false) (hf : fieldAt Fs k = A) :
    x ∈ truncW (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
        (Ed (mkM P (upd μ fd.fref (famOfD P μ fd D)))
          (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ (push pre (push ps ρ0)) A)) ↔
      nonrecOkF P μ fd σ (push ps ρ0) Fs k pre x := by
  show _ ↔ x ∈ truncW (mkM P μ) W4 (evalTotal σ fd.resLevel)
      (Ed (mkM P μ) (den (mkM P μ) σ (push pre (push ps ρ0)) (fieldAt Fs k)))
  rw [hf, den_off P μ fd.fref (famOfD P μ fd D) σ (push pre (push ps ρ0)) hA]
  exact Iff.rfl

/-- `x ∈ truncW … S` puts `x` in the stage `W4 k`. -/
theorem truncW_mem_W4 {μ' : Nat → List Nat → PSet.{4}} {k : Nat} {S x : PSet.{4}}
    (h : x ∈ truncW (mkM P μ') W4 k S) : x ∈ W4 k := by
  unfold truncW cond at h
  split at h
  · rename_i hS; exact (stageW4 P k).trans hS h
  · exact absurd h not_mem_pempty

include hB hpf hD1 hD2 hD3 hD4
/-- L0: a recursive occurrence at depth `pre.length` denotes the `fibAt` of `D`
    at the parameter prefix. -/
theorem ed_recOcc (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (idx : List (Expr Nat)) (hidx : idx.length = fd.indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst fd.fref e = false) :
    Equiv (Ed (mkM P (upd μ fd.fref (famOfD P μ fd D)))
        (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ (push pre (push ps ρ0))
          (foldApps (.const fd.fref (canonL ar))
            (policyParameterLocals fd.params.length pre.length ++ idx))))
      (sep (fun z => Equiv (resTupF P μ fd σ (push ps ρ0) z)
          (recTupAt P μ fd σ (push pre (push ps ρ0))
            (foldApps (.const fd.fref (canonL ar))
              (policyParameterLocals fd.params.length pre.length ++ idx))))
        (D σ (push ps ρ0))) := by
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
    · rw [← hps]
      have hd := den_paramLocals (mkM P μ) σ ps pre ρ0
      rw [he] at hd
      exact hd
  cases P.dec (argsFitF P μ fd σ ρ' A') with
  | isTrue hfit =>
      have htf : TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
          (args.map (den (mkM P μ) σ ρ')) :=
        (argsFitF_directRec P μ fd σ ρ' fd.fref (canonL ar) args).mp hfit
      have e1 := ed_recApp_fit P μ fd ar (hpi_of fd ar hB) hpf
        (famOfD P μ fd D) μ (famEndD P μ fd D)
        (fun _ => rfl) (fun _ _ _ => rfl)
        (fun σ' => famEndD_envResp P μ fd D hD1 σ')
        (famEndD_levels P μ fd D hB hD1 hD2)
        σ ρ' args hargs htf
      rw [hmap] at e1
      -- e1 : Ed MD (…) ≈ Ed (mkM P μ) (famEndD σ (push (ps ++ idxv) ρ0))
      refine e1.trans ((ed_famEndD P μ fd D hD3 μ σ (push (ps ++ idx.map (den (mkM P μ) σ ρ')) ρ0)).trans ?_)
      -- fibAt σ (shiftρ nq ρ') (lastVals nq ρ') = fibAt σ (push ps ρ0) idxv
      show Equiv (fibAt P μ fd D σ _ _) (sep (fun z => Equiv (resTupF P μ fd σ (push ps ρ0) z)
          (recTupAt P μ fd σ ρ' A')) (D σ (push ps ρ0)))
      have hidxv : (idx.map (den (mkM P μ) σ ρ')).length = fd.indices.length :=
        (List.length_map _ _).trans hidx
      rw [push_append, ← hidxv, shiftρ_push, lastVals_push]
      unfold fibAt recTupAt
      rw [cond_pos hfit, familyIdx_directRec]
      exact Equiv.rfl
  | isFalse hnf =>
      have hnf' : ¬ TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
          (args.map (den (mkM P μ) σ ρ')) :=
        fun h => hnf ((argsFitF_directRec P μ fd σ ρ' fd.fref (canonL ar) args).mpr h)
      have hl : args.length = (fd.params ++ fd.indices).length := by
        show (policyParameterLocals fd.params.length pre.length ++ idx).length = _
        rw [List.length_append, length_paramLocals, hidx, List.length_append]

      have e1 := ed_recApp_nofit P μ fd ar (hpi_of fd ar hB) hpf
        (famOfD P μ fd D) μ (famEndD P μ fd D)
        (fun _ => rfl) (fun _ _ _ => rfl)
        (fun σ' => famEndD_envResp P μ fd D hD1 σ')
        σ ρ' args hargs hl hnf'
      have hsep : Equiv (sep (fun z => Equiv (resTupF P μ fd σ (push ps ρ0) z)
          (recTupAt P μ fd σ ρ' A')) (D σ (push ps ρ0))) pempty := by
        apply ext; intro z; constructor
        · intro hz
          obtain ⟨i, hi, _⟩ := mem_sep.mp hz
          have hrec : recTupAt P μ fd σ ρ' A' = singleton pempty := by
            unfold recTupAt; exact cond_neg hnf _ _
          rw [hrec] at hi
          exact absurd hi (resTupF_ne_sentinel P μ fd σ (push ps ρ0) _)
        · intro hz; exact absurd hz not_mem_pempty
      exact e1.trans hsep.symm

/-- L1: a directly recursive field denotes the `fibAt`-fit subset of `D`,
    truncated at the table level. -/
theorem truncW_direct_field (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length) (A : Expr Nat) (x : PSet.{4})
    (hA : DirectRec fd.fref ar fd.params.length fd.indices.length pre.length A) :
    x ∈ truncW (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
        (Ed (mkM P (upd μ fd.fref (famOfD P μ fd D)))
          (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ (push pre (push ps ρ0)) A)) ↔
      x ∈ D σ (push ps ρ0) ∧
        Equiv (resTupF P μ fd σ (push ps ρ0) x)
          (recTupAt P μ fd σ (push pre (push ps ρ0)) A) := by
  obtain ⟨idx, hAe, hidx, hfree⟩ := hA
  rw [hAe]
  have e1 := ed_recOcc P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps pre hps idx hidx hfree
  have hW : sep (fun z => Equiv (resTupF P μ fd σ (push ps ρ0) z)
      (recTupAt P μ fd σ (push pre (push ps ρ0))
        (foldApps (.const fd.fref (canonL ar))
          (policyParameterLocals fd.params.length pre.length ++ idx))))
      (D σ (push ps ρ0)) ∈ W4 (evalTotal σ fd.resLevel) :=
    (stageW4 P _).subset (hD4 σ (push ps ρ0)) (fun _ => mem_sep_subset)
  rw [truncW_of_mem (mem_congr_left e1.symm hW)]
  constructor
  · intro hx
    obtain ⟨i, hpi, hix⟩ := mem_sep.mp (mem_congr_right e1 hx)
    exact ⟨mem_congr_left hix ⟨i, Equiv.refl _⟩,
      (resTupF_congr P μ fd σ (push ps ρ0) hix.symm).trans hpi⟩
  · rintro ⟨hxD, hxt⟩
    obtain ⟨i, hix⟩ := hxD
    exact mem_congr_right e1.symm (mem_sep.mpr ⟨i,
      (resTupF_congr P μ fd σ (push ps ρ0) hix).trans hxt, hix⟩)

/-- L2: a function-recursive field denotes the `piSet` of its domain over the
    `semF`-fibres, truncated at the table level. -/
theorem truncW_fn_field (σ : Nat → Nat) (ps pre : List PSet.{4})
    (hps : ps.length = fd.params.length) (Fs : List (Expr Nat)) (k : Nat)
    (A : Expr Nat) (x : PSet.{4})
    (hf : fieldAt Fs k = A) (hpre : pre.length = k)
    (hA : FnRec fd.fref ar fd.params.length fd.indices.length pre.length A) :
    x ∈ truncW (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
        (Ed (mkM P (upd μ fd.fref (famOfD P μ fd D)))
          (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ (push pre (push ps ρ0)) A)) ↔
      x ∈ piSet (domBigF P μ fd σ (push ps ρ0) Fs k pre)
        (Sem.fib (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0)) k pre) := by
  obtain ⟨D', idx, hAe, hidx, hD', hfree⟩ := hA
  let ρ' := push pre (push ps ρ0)
  let ρp := push ps ρ0
  let MD := mkM P (upd μ fd.fref (famOfD P μ fd D))
  let B := foldApps (.const fd.fref (canonL ar))
    (policyParameterLocals fd.params.length (pre.length + 1) ++ idx)
  have hvey : ∀ y : PSet.{4}, vcons y ρ' = push (pre ++ [y]) ρp :=
    fun y => (push_append pre [y] ρp).symm
  have hlen' : ∀ y : PSet.{4}, (pre ++ [y]).length = pre.length + 1 :=
    fun _ => by rw [List.length_append, List.length_singleton]
  -- the recursive fibres never contain `∅` (subsets of `D`)
  have hno : ∀ y : PSet.{4}, ¬ pempty ∈ Ed MD (den MD σ (vcons y ρ') B) := by
    intro y h0
    rw [hvey y] at h0
    have e1 := ed_recOcc P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps (pre ++ [y])
      hps idx hidx hfree
    rw [hlen' y] at e1
    obtain ⟨i, _, hiz⟩ := mem_sep.mp (mem_congr_right e1 h0)
    exact hD3 σ ρp _ ⟨i, Equiv.refl _⟩ hiz
  -- fibre denotation is the L0 `sep`
  have eSep : ∀ y : PSet.{4}, Equiv (Ed MD (den MD σ (vcons y ρ') B))
      (sep (fun z => Equiv (resTupF P μ fd σ ρp z)
        (recTupAt P μ fd σ (vcons y ρ') B)) (D σ ρp)) := by
    intro y
    have e1 := ed_recOcc P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps (pre ++ [y])
      hps idx hidx hfree
    rw [hlen' y, ← hvey y] at e1
    exact e1
  -- `Ed` of the domain is `domEF`'s value
  have hdomE : domEF P μ σ ρp Fs k pre =
      Ed (mkM P μ) (den (mkM P μ) σ ρ' D') := by
    unfold domEF
    rw [hf, hAe]
    show Ed (mkM P μ) (den (mkM P μ) σ ρ' (piDom (.pi D' B))) = _
    dsimp only [piDom]
  have hEdE : Equiv (Ed MD (den MD σ ρ' D'))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ' D')) := by
    rw [den_off P μ fd.fref (famOfD P μ fd D) σ ρ' hD']
    exact Equiv.rfl
  have hfibEd : ∀ a a', Equiv a a' →
      Equiv (Ed MD (den MD σ (vcons a ρ') B)) (Ed MD (den MD σ (vcons a' ρ') B)) :=
    fun a a' h => ed_congr MD (den_congr MD σ B (vcons_congr h (fun i => Equiv.refl (ρ' i))))
  have ePi : Equiv (Ed MD (piVal MD (den MD σ ρ' D')
        (fun y => den MD σ (vcons y ρ') B)))
      (piSet (Ed MD (den MD σ ρ' D')) (fun y => Ed MD (den MD σ (vcons y ρ') B))) :=
    ed_piVal_of_noEmpty (M := MD) (A := den MD σ ρ' D')
      (fun x' x'' hx => den_congr MD σ B (vcons_congr hx (fun i => Equiv.refl (ρ' i))))
      (fun y _ => hno y)
  rw [hAe]
  show _ ↔ x ∈ piSet (domBigF P μ fd σ ρp Fs k pre)
      (fun y => sep (fun z => Equiv ((semF P μ fd σ ρp Fs).resTup z)
        ((semF P μ fd σ ρp Fs).recTup k pre y)) (D σ ρp))
  cases P.dec (domEF P μ σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel)) with
  | isTrue hEW =>
      have hdomB : domBigF P μ fd σ ρp Fs k pre = domEF P μ σ ρp Fs k pre := by
        unfold domBigF
        rw [hf, kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩]
        exact cond_pos hEW _ _
      have hrec : ∀ y, recTupF P μ fd σ ρp Fs k pre y =
          recTupAt P μ fd σ (vcons y ρ') B := by
        intro y
        unfold recTupF
        rw [hf, kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩, hAe]
        exact cond_pos hEW _ _
      have hE2 : Equiv (domEF P μ σ ρp Fs k pre)
          (Ed (mkM P μ) (den (mkM P μ) σ ρ' D')) := by rw [hdomE]; exact Equiv.rfl
      have hrecE : ∀ a a', Equiv a a' →
          Equiv (recTupF P μ fd σ ρp Fs k pre a) (recTupAt P μ fd σ (vcons a' ρ') B) := by
        intro a a' h
        rw [hrec a]
        exact recTupAt_congr P μ fd σ (vcons_congr h (fun i => Equiv.refl (ρ' i))) B
      -- `Ed` of the pi is in the stage
      have hpiW : piSet (Ed MD (den MD σ ρ' D'))
          (fun y => Ed MD (den MD σ (vcons y ρ') B)) ∈ W4 (evalTotal σ fd.resLevel) :=
        (stageW4 P (evalTotal σ fd.resLevel)).pi hfibEd (mem_congr_left hEdE.symm (hdomE.symm ▸ hEW))
          (fun y _ => mem_congr_left (eSep y).symm
            ((stageW4 P (evalTotal σ fd.resLevel)).subset (hD4 σ ρp) (fun _ => mem_sep_subset)))
      have hEdA : Ed (mkM P (upd μ fd.fref (famOfD P μ fd D)))
          (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ ρ' (.pi D' B))
          ∈ W4 (evalTotal σ fd.resLevel) := mem_congr_left ePi.symm hpiW
      rw [truncW_of_mem hEdA, hdomB]
      have hpi : Equiv (piSet (domEF P μ σ ρp Fs k pre)
          (fun y => sep (fun z => Equiv ((semF P μ fd σ ρp Fs).resTup z)
            ((semF P μ fd σ ρp Fs).recTup k pre y)) (D σ ρp)))
          (piSet (Ed MD (den MD σ ρ' D'))
            (fun y => Ed MD (den MD σ (vcons y ρ') B))) :=
        piSet_congr (hE2.trans hEdE.symm) (fun a a' h =>
          ((sep_congr
            (fun z z' hzz hh => ((resTupF_congr P μ fd σ ρp hzz.symm).trans hh).trans
              (hrecE a a' h))
            (fun z z' hzz hh => ((resTupF_congr P μ fd σ ρp hzz.symm).trans hh).trans
              (hrecE a a' h).symm)
            Equiv.rfl).trans (eSep a').symm))
      exact ⟨fun hx => mem_congr_right hpi.symm (mem_congr_right ePi hx),
        fun hx => mem_congr_right ePi.symm (mem_congr_right hpi hx)⟩
  | isFalse hnE =>
      constructor
      · intro hx
        have hxS : x ∈ Ed MD (den MD σ ρ' (.pi D' B)) := truncW_sub hx
        have hxW : x ∈ W4 (evalTotal σ fd.resLevel) := truncW_mem_W4 P hx
        have hxP := mem_congr_right ePi hxS
        have hgd := isFuncOnDep_of_mem_piSet hfibEd hxP
        have hsub : Subset (Ed MD (den MD σ ρ' D')) (sUnion (sUnion x)) := by
          intro a ha
          obtain ⟨b, _, hab⟩ := hgd.1 a ha
          exact mem_sUnion.mpr ⟨singleton a,
            mem_sUnion.mpr ⟨ordPair a b, hab, mem_pair.mpr (Or.inl Equiv.rfl)⟩,
            mem_singleton.mpr Equiv.rfl⟩
        have hEW' : Ed MD (den MD σ ρ' D') ∈ W4 (evalTotal σ fd.resLevel) :=
          (stageW4 P (evalTotal σ fd.resLevel)).subset ((stageW4 P (evalTotal σ fd.resLevel)).sUnion ((stageW4 P (evalTotal σ fd.resLevel)).sUnion hxW)) hsub
        exact absurd (hdomE ▸ mem_congr_left hEdE hEW') hnE
      · intro hx
        have hdomB : domBigF P μ fd σ ρp Fs k pre = singleton pempty := by
          unfold domBigF
          rw [hf, kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩]
          exact cond_neg hnE _ _
        have hrecF : recTupF P μ fd σ ρp Fs k pre pempty = singleton pempty := by
          unfold recTupF
          rw [hf, kindOf_fnRec ⟨D', idx, hAe, hidx, hD', hfree⟩]
          exact cond_neg hnE _ _
        rw [hdomB] at hx
        have hgd' := isFuncOnDep_of_mem_piSet
          (fun a a' h => sep_congr
            (fun z z' hzz hh => ((resTupF_congr P μ fd σ ρp hzz.symm).trans hh).trans
              (recTupF_congr P μ fd σ ρp Fs k (LEq.refl pre) h))
            (fun z z' hzz hh => ((resTupF_congr P μ fd σ ρp hzz.symm).trans hh).trans
              (recTupF_congr P μ fd σ ρp Fs k (LEq.refl pre) h.symm))
            Equiv.rfl)
          hx
        obtain ⟨b, hb, _⟩ := hgd'.1 pempty (mem_singleton.mpr Equiv.rfl)
        obtain ⟨i, hi, _⟩ := mem_sep.mp hb
        rw [hrecF] at hi
        exact absurd hi (resTupF_ne_sentinel P μ fd σ ρp _)

/-- The telescope fit at the `famOfD`-table reads as the `semF` `InPhi` walk. -/
theorem telFitsT_iff_InPhi_gen (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest done.length →
      (TelFitsT (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
          σ rest (push pre (push ps ρ0)) xs ↔
        Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
          (kindsOf fd.fref rest) xs done.length pre) := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls
      cases xs with
      | nil => exact ⟨fun _ => trivial, fun _ => trivial⟩
      | cons x xs' => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls
      obtain ⟨hdisj, hcls'⟩ := hcls
      have hf : fieldAt Fs done.length = A := by
        rw [hFs]
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      show _ ↔ Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
        (kindOf fd.fref A :: kindsOf fd.fref rest') xs done.length pre
      rcases hdisj with h | h | h
      · rw [kindOf_free h]
        cases xs with
        | nil => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
        | cons x xs' =>
            refine and_congr (truncW_plain_field P μ fd D σ ps pre Fs done.length A x h hf) ?_
            exact (step done A rest' pre x xs' hFs hpre hcls' IH)
      · rw [kindOf_directRec h]
        cases xs with
        | nil => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
        | cons x xs' =>
            have hrecD : (semF P μ fd σ (push ps ρ0) Fs).recTup done.length pre pempty =
                recTupAt P μ fd σ (push pre (push ps ρ0)) A := by
              show recTupF P μ fd σ (push ps ρ0) Fs done.length pre pempty = _
              unfold recTupF
              rw [hf, kindOf_directRec h]
            show _ ↔ ((x ∈ D σ (push ps ρ0) ∧
                Equiv ((semF P μ fd σ (push ps ρ0) Fs).resTup x)
                  ((semF P μ fd σ (push ps ρ0) Fs).recTup done.length pre pempty)) ∧
              Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
                (kindsOf fd.fref rest') xs' (done.length + 1) (pre ++ [x]))
            rw [hrecD]
            exact and_congr (truncW_direct_field P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps pre hps A x (hpre ▸ h))
              (step done A rest' pre x xs' hFs hpre hcls' IH)
      · rw [kindOf_fnRec h]
        cases xs with
        | nil => exact ⟨fun h => False.elim h, fun h => False.elim h⟩
        | cons x xs' =>
            exact and_congr (truncW_fn_field P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps pre hps Fs done.length A x hf hpre (hpre ▸ h))
              (step done A rest' pre x xs' hFs hpre hcls' IH)
  where
    step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClassA fd.fref ar fd.params.length fd.indices.length rest' (done.length + 1))
        (IH : ∀ (done : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done ++ rest' → pre.length = done.length →
          FieldsClassA fd.fref ar fd.params.length fd.indices.length rest' done.length →
          (TelFitsT (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
              σ rest' (push pre (push ps ρ0)) xs ↔
            Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
              (kindsOf fd.fref rest') xs done.length pre)) :
        TelFitsT (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
            σ rest' (vcons x (push pre (push ps ρ0))) xs' ↔
          Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
            (kindsOf fd.fref rest') xs' (done.length + 1) (pre ++ [x]) := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x]) (push ps ρ0) :=
        (push_append pre [x] (push ps ρ0)).symm
      have hFs' : Fs = (done ++ [A]) ++ rest' :=
        hFs.trans (List.append_assoc done [A] rest').symm
      have hlen' : (pre ++ [x]).length = (done ++ [A]).length := by
        rw [List.length_append, List.length_append, hpre]
        rfl
      have hcls'' : FieldsClassA fd.fref ar fd.params.length fd.indices.length
          rest' (done ++ [A]).length := by
        rw [List.length_append]; exact hcls'
      have e := IH (done ++ [A]) (pre ++ [x]) xs' hFs' hlen' hcls''
      rw [List.length_append] at e
      rw [← hvey] at e
      exact e

/-- Top-level telescope dictionary: `TelFitsT` at `ρp = push ps ρ0` ⟺ `InPhi`. -/
theorem telFitsT_iff_InPhi (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length) (Fs : List (Expr Nat))
    (hcls : FieldsClassA fd.fref ar fd.params.length fd.indices.length Fs 0)
    (xs : List PSet.{4}) :
    TelFitsT (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
        σ Fs (push ps ρ0) xs ↔
      Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) (D σ (push ps ρ0))
        (kindsOf fd.fref Fs) xs 0 [] :=
  telFitsT_iff_InPhi_gen P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps hps Fs [] Fs [] xs rfl rfl hcls

/-- The constructor fibre at the `famOfD`-table reads `InPhi` of `semF`. -/
theorem mem_TypeFib_famOfD (σ : Nat → Nat) (ps : List PSet.{4})
    (hps : ps.length = fd.params.length)
    (hclsA : ∀ c, c ∈ fd.ctors →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length c.1 0)
    (hri : ∀ c, c ∈ fd.ctors → ∀ e, e ∈ c.2 → occursConst fd.fref e = false)
    (is : List PSet.{4}) (z : PSet.{4}) :
    z ∈ TypeFib (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel)
        σ fd.ctors (push ps ρ0) is ↔
      ∃ j c xs, fd.ctors[j]? = some c ∧
        Sem.InPhi (semF P μ fd σ (push ps ρ0) c.1) (D σ (push ps ρ0))
          (kindsOf fd.fref c.1) xs 0 [] ∧
        LEq (c.2.map (den (mkM P μ) σ (push xs (push ps ρ0)))) is ∧
        Equiv z (dataVal j xs) := by
  have hmap : ∀ c xs, c ∈ fd.ctors →
      c.2.map (den (mkM P (upd μ fd.fref (famOfD P μ fd D))) σ (push xs (push ps ρ0))) =
      c.2.map (den (mkM P μ) σ (push xs (push ps ρ0))) := fun c xs hc =>
    List.map_congr_left (fun e he =>
      den_off P μ fd.fref (famOfD P μ fd D) σ (push xs (push ps ρ0)) (hri c hc e he))
  constructor
  · intro h
    obtain ⟨j, c, xs, hcj, hT, hL, hz⟩ := (mem_TypeFib_iff
      (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel) σ
        fd.ctors (push ps ρ0) is).mp h
    have hc : c ∈ fd.ctors := List.getElem?_mem hcj
    rw [hmap c xs hc] at hL
    exact ⟨j, c, xs, hcj,
      (telFitsT_iff_InPhi P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps hps c.1 (hclsA c hc) xs).mp hT, hL, hz⟩
  · rintro ⟨j, c, xs, hcj, hT, hL, hz⟩
    have hc : c ∈ fd.ctors := List.getElem?_mem hcj
    rw [← hmap c xs hc] at hL
    exact (mem_TypeFib_iff
      (mkM P (upd μ fd.fref (famOfD P μ fd D))) W4 (evalTotal σ fd.resLevel) σ
        fd.ctors (push ps ρ0) is).mpr ⟨j, c, xs, hcj,
          (telFitsT_iff_InPhi P μ fd ar D hB hpf hD1 hD2 hD3 hD4 σ ps hps c.1 (hclsA c hc) xs).mpr hT, hL, hz⟩

end

end PSet

end Rcic.F3
