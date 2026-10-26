import rcic.RcicF3KTWLfp

/-!
# F3 S7 KT-2b-4b-1: packaging — `lfp_of_big` and `NonIRSem`.

`sigOfBig` packages a `Fin n`-family of `BigDoms`/`Sem` pairs into a `GSig`;
`lfp_of_big` shows the `sep`-form operator over a bounding set `B` has
`lift (gSet (sigOfBig …))` as its least fixed point.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

/-- The guarded signature of a `Fin n`-family of big-domain/semantics pairs. -/
noncomputable def sigOfBig (ch : Choice.{u}) {n : Nat} (G : Fin n → BigDoms.{u, v})
    (Sm : Fin n → Sem.{max u v}) : GSig.{u} :=
  GSig.sum (fun j : ULift.{u} (Fin n) =>
    ((G j.down).toPlain ch).layout j.down.val |>.sig (Sm j.down))

/-- The `sep`-form operator over `B` has `lift (gSet (sigOfBig …))` as lfp. -/
theorem lfp_of_big (ch : Choice.{u}) {n : Nat} (G : Fin n → BigDoms.{u, v})
    (Sm : Fin n → Sem.{max u v})
    (H : ∀ j, BigHyp (G j) (Sm j)) (B : PSet.{max u v})
    (hcov : ∀ (j : Fin n) (X : PSet.{u}) (xs : List PSet.{max u v}),
      (Sm j).InPhi (lift.{u, v} X) (G j).kinds xs 0 [] → dataVal j.val xs ∈ B)
    (Ψ : PSet.{max u v} → PSet.{max u v})
    (hΨ : ∀ X, Equiv (Ψ X) (sep (fun z => ∃ j : Fin n, ∃ xs, Equiv z (dataVal j.val xs) ∧
        (Sm j).InPhi X (G j).kinds xs 0 []) B))
    (hmono : ∀ X Y, Sub X Y → Sub (Ψ X) (Ψ Y)) :
    IsLfp Ψ (lift.{u, v} (gSet (sigOfBig ch G Sm))) := by
  let L := fun j : ULift.{u} (Fin n) => ((G j.down).toPlain ch).layout j.down.val
  have hW : WShaped.{u, v}
      (fun X => iUnionT.{u, v} (fun j => phiSpec (L j) (Sm j.down) B X))
      (sigOfBig ch G Sm) :=
    wshaped_phiSpec_sum L (fun j => Sm j.down)
      (fun j => PlainDoms.cover ((G j.down).toPlain ch) j.down.val (Sm j.down)
        (BigHyp.toPlain ch (H j.down)) (hcov j.down)) ch
  have hΦ : ∀ X, Equiv (iUnionT.{u, v} (fun j => phiSpec (L j) (Sm j.down) B X)) (Ψ X) := by
    intro X
    have hE : iUnionT.{u, v} (fun j => phiSpec (L j) (Sm j.down) B X) =
        iUnionT.{u, v}
          (fun j : ULift.{u} (Fin n) => phiK j.down.val (G j.down).kinds (Sm j.down) B X) :=
      congrArg iUnionT (funext fun j => phiSpec_eq_phiK (L j) (Sm j.down) B X)
    rw [hE]
    exact (iUnionT_phiK_fin (fun j : Fin n => (G j).kinds) Sm B X).trans (hΨ X).symm
  exact IsLfp.of_wshaped (wshaped_congr hΦ hW) hmono

/-- Semantic locality (non-IR) at the `R-CIC` table: each `den` of `fieldAt`/
`piDom` depends only on the plain prefix values. -/
def NonIRSem (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (σ : Nat → Nat)
    (ρp : Nat → PSet.{4}) (f : Nat) (Fs : List (Expr Nat)) : Prop :=
  ∀ k, k < Fs.length → ∀ pre pre' : List PSet.{4}, pre.length = k → pre'.length = k →
    LEq (plainVals ((kindsOf f Fs).take k) pre) (plainVals ((kindsOf f Fs).take k) pre') →
    Equiv (den (mkM P μ) σ (push pre ρp) (fieldAt Fs k))
        (den (mkM P μ) σ (push pre' ρp) (fieldAt Fs k)) ∧
    Equiv (den (mkM P μ) σ (push pre ρp) (piDom (fieldAt Fs k)))
        (den (mkM P μ) σ (push pre' ρp) (piDom (fieldAt Fs k)))

/-- The truncated field domain — the `nonrecOkF` bound set. -/
def bigPF (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) : PSet.{4} :=
  truncW (mkM P μ) W4 (evalTotal σ fd.resLevel)
    (Ed (mkM P μ) (den (mkM P μ) σ (push pre ρp) (fieldAt Fs k)))

/-- `bigPF` is a stage member. -/
theorem bigPF_mem_W4 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) : bigPF P μ fd σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel) :=
  truncW_mem (mkM P μ) _ (stageW4 P _)

/-- `kindsOf` at index `k` reads `kindOf` of `fieldAt Fs k`. -/
theorem kindsOf_getElem? {f : Nat} {Fs : List (Expr Nat)} {k : Nat} {p : PKind}
    (h : (kindsOf f Fs)[k]? = some p) : k < Fs.length ∧ kindOf f (fieldAt Fs k) = p := by
  have hm := List.getElem?_map (kindOf f) Fs k ▸ h
  cases hF : Fs[k]? with
  | none => rw [hF] at hm; exact absurd hm Option.noConfusion
  | some e =>
      rw [hF] at hm
      have he : kindOf f e = p := (Option.some.injEq _ _).mp hm
      have hF' : Fs.get? k = some e := (List.get?_eq_getElem? Fs k) ▸ hF
      have hget : fieldAt Fs k = e := by
        show Fs.getD k (.sort .zero) = e
        unfold List.getD
        rw [hF']; rfl
      exact ⟨(List.getElem?_eq_some.mp hF).1, hget ▸ he⟩

/-- `bigPF` respects the plain-prefix locality. -/
theorem bigPF_loc (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {Fs : List (Expr Nat)}
    (hN : NonIRSem P μ σ ρp fd.fref Fs)
    {k : Nat} (hk : (kindsOf fd.fref Fs)[k]? = some .plain)
    {pre pre' : List PSet.{4}} (hpre : pre.length = k) (hpre' : pre'.length = k)
    (hle : LEq (plainVals ((kindsOf fd.fref Fs).take k) pre)
      (plainVals ((kindsOf fd.fref Fs).take k) pre')) :
    Equiv (bigPF P μ fd σ ρp Fs k pre) (bigPF P μ fd σ ρp Fs k pre') :=
  truncW_congr (mkM P μ) W4 (evalTotal σ fd.resLevel)
    (ed_congr (mkM P μ)
      ((hN k (kindsOf_getElem? hk).1 pre pre' hpre hpre' hle).1))

/-- `domBigF` respects the plain-prefix locality. -/
theorem domBigF_loc (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) {Fs : List (Expr Nat)}
    (hN : NonIRSem P μ σ ρp fd.fref Fs)
    {k : Nat} (hk : (kindsOf fd.fref Fs)[k]? = some .fn)
    {pre pre' : List PSet.{4}} (hpre : pre.length = k) (hpre' : pre'.length = k)
    (hle : LEq (plainVals ((kindsOf fd.fref Fs).take k) pre)
      (plainVals ((kindsOf fd.fref Fs).take k) pre')) :
    Equiv (domBigF P μ fd σ ρp Fs k pre) (domBigF P μ fd σ ρp Fs k pre') := by
  have hk' : kindOf fd.fref (fieldAt Fs k) = .fn := (kindsOf_getElem? hk).2
  unfold domBigF
  rw [hk']
  exact cond_congr
    ⟨fun hm => mem_congr_left
      (ed_congr (mkM P μ) ((hN k (kindsOf_getElem? hk).1 pre pre' hpre hpre' hle).2)) hm,
      fun hm => mem_congr_left
      (ed_congr (mkM P μ) ((hN k (kindsOf_getElem? hk).1 pre pre' hpre hpre' hle).2)).symm hm⟩
    (ed_congr (mkM P μ) ((hN k (kindsOf_getElem? hk).1 pre pre' hpre hpre' hle).2)) Equiv.rfl

/-- At a `.direct` field, `domBigF` is `{∅}`. -/
theorem domBigF_direct (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat)) (k : Nat)
    (pre : List PSet.{4}) (hk : kindOf fd.fref (fieldAt Fs k) = .direct) :
    domBigF P μ fd σ ρp Fs k pre = singleton pempty := by
  unfold domBigF
  rw [hk]

/-- `PsiF` written in the `lfp_of_big` `hΨ`-form (the constructor-indexed
`sep` over `W4`). -/
theorem PsiF_finK (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (X : PSet.{4}) :
    Equiv (PsiF P μ fd σ ρp X)
      (sep (fun z => ∃ j : Fin fd.ctors.length, ∃ xs, Equiv z (dataVal j.val xs) ∧
          (semF P μ fd σ ρp (fd.ctors.get j).1).InPhi X
            (kindsOf fd.fref (fd.ctors.get j).1) xs 0 [])
        (W4 (evalTotal σ fd.resLevel))) := PsiF_fin P μ fd σ ρp X

/-- Constructor data land in `W4` when the base set `X'` does and the guards do. -/
theorem hcovF (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat))
    {X' : PSet.{4}} (hX' : X' ∈ W4 (evalTotal σ fd.resLevel)) (j : Nat)
    (xs : List PSet.{4}) :
    Sem.InPhi (semF P μ fd σ ρp Fs) X' (kindsOf fd.fref Fs) xs 0 [] →
      dataVal j xs ∈ W4 (evalTotal σ fd.resLevel) := fun hIn =>
  dataVal_mem_stage (stageW4 P _) j xs
    (InPhi_mem_stage (stageW4 P _) (semF P μ fd σ ρp Fs) hX'
      (fun k pre x hnok => nonrecOkF_mem_W4 P μ fd σ ρp Fs k pre x hnok)
      (fun k pre => domBigF_mem_W4 P μ fd σ ρp Fs k pre)
      (kindsOf fd.fref Fs) xs 0 [] hIn)

/-- `Small` from `W4`-membership under the `W4 kk = univIn` identification. -/
theorem small_of_mem_W4_0 (fd : FamData) {σ : Nat → Nat}
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{0, 4}) {x : PSet.{4}}
    (h : x ∈ W4 (evalTotal σ fd.resLevel)) : Small.{0, 4} x := by
  rw [hW] at h
  exact mem_univIn.{0, 4}.mp h

/-- The `u = 0` `BigDoms` for a constructor's field list. -/
noncomputable def bigDomsF0 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (hW : W4 (evalTotal σ fd.resLevel) = univIn.{0, 4}) :
    BigDoms.{0, 4} where
  kinds := kindsOf fd.fref Fs
  bigP := bigPF P μ fd σ ρp Fs
  bigR := domBigF P μ fd σ ρp Fs
  smallP := fun k pre => small_of_mem_W4_0 fd hW (bigPF_mem_W4 P μ fd σ ρp Fs k pre)
  smallR := fun k pre => small_of_mem_W4_0 fd hW (domBigF_mem_W4 P μ fd σ ρp Fs k pre)

/-- The guarded signature of the `u = 0` family packaging. -/
noncomputable def sigF0 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{0, 4}) : GSig.{0} :=
  sigOfBig.{0, 4} P.c0
    (fun j : Fin fd.ctors.length => bigDomsF0 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1)

/-- `lift (gSet (sigF0 …))` is the least fixed point of `PsiF`, and it is a
member of the `W4` bound. -/
theorem lfpF0 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{0, 4})
    (hN : ∀ j : Fin fd.ctors.length,
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    IsLfp (PsiF P μ fd σ ρp) (lift.{0, 4} (gSet (sigF0 P μ fd σ ρp hW))) ∧
      lift.{0, 4} (gSet (sigF0 P μ fd σ ρp hW)) ∈ W4 (evalTotal σ fd.resLevel) := by
  refine ⟨?_, hW ▸ mem_univIn.{0, 4}.mpr (small_lift.{0, 4} _)⟩
  refine lfp_of_big.{0, 4} P.c0
    (fun j : Fin fd.ctors.length => bigDomsF0 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1) ?_ (W4 (evalTotal σ fd.resLevel)) ?_
    (PsiF P μ fd σ ρp) (fun X => (PsiF_finK P μ fd σ ρp X).trans
      (sep_congr
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (Equiv.refl _)))
    (fun X Y h => PsiF_mono P μ fd σ ρp h)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k pre x hk hlen hnok
      show x ∈ bigPF P μ fd σ ρp (fd.ctors.get j).1 k pre
      exact hnok
    · intro k pre pre' hk hlen hlen' hle
      exact bigPF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .plain from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk hlen
      show Equiv (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
        ((semF P μ fd σ ρp (fd.ctors.get j).1).domBig k pre)
      exact Equiv.rfl
    · intro k pre pre' hk hlen hlen' hle
      exact domBigF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .fn from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk
      show Equiv (lift.{0, 4} (singleton pempty)) (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
      rw [domBigF_direct P μ fd σ ρp (fd.ctors.get j).1 k pre
        (kindsOf_getElem? hk).2]
      exact (lift_singleton_equiv.{0, 4} pempty).trans
        (singleton_congr (lift_pempty_equiv.{0, 4}))
  · intro j X xs hIn
    exact hcovF P μ fd σ ρp (fd.ctors.get j).1
      (hW ▸ mem_univIn.{0, 4}.mpr (small_lift.{0, 4} X)) j.val xs hIn

/-- `Small` from `W4`-membership under the `W4 kk = univIn` identification. -/
theorem small_of_mem_W4_1 (fd : FamData) {σ : Nat → Nat}
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{1, 4}) {x : PSet.{4}}
    (h : x ∈ W4 (evalTotal σ fd.resLevel)) : Small.{1, 4} x := by
  rw [hW] at h
  exact mem_univIn.{1, 4}.mp h

/-- The `u = 1` `BigDoms` for a constructor's field list. -/
noncomputable def bigDomsF1 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (hW : W4 (evalTotal σ fd.resLevel) = univIn.{1, 4}) :
    BigDoms.{1, 4} where
  kinds := kindsOf fd.fref Fs
  bigP := bigPF P μ fd σ ρp Fs
  bigR := domBigF P μ fd σ ρp Fs
  smallP := fun k pre => small_of_mem_W4_1 fd hW (bigPF_mem_W4 P μ fd σ ρp Fs k pre)
  smallR := fun k pre => small_of_mem_W4_1 fd hW (domBigF_mem_W4 P μ fd σ ρp Fs k pre)

/-- The guarded signature of the `u = 1` family packaging. -/
noncomputable def sigF1 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{1, 4}) : GSig.{1} :=
  sigOfBig.{1, 4} P.c1
    (fun j : Fin fd.ctors.length => bigDomsF1 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1)

/-- `lift (gSet (sigF1 …))` is the least fixed point of `PsiF`, and it is a
member of the `W4` bound. -/
theorem lfpF1 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{1, 4})
    (hN : ∀ j : Fin fd.ctors.length,
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    IsLfp (PsiF P μ fd σ ρp) (lift.{1, 4} (gSet (sigF1 P μ fd σ ρp hW))) ∧
      lift.{1, 4} (gSet (sigF1 P μ fd σ ρp hW)) ∈ W4 (evalTotal σ fd.resLevel) := by
  refine ⟨?_, hW ▸ mem_univIn.{1, 4}.mpr (small_lift.{1, 4} _)⟩
  refine lfp_of_big.{1, 4} P.c1
    (fun j : Fin fd.ctors.length => bigDomsF1 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1) ?_ (W4 (evalTotal σ fd.resLevel)) ?_
    (PsiF P μ fd σ ρp) (fun X => (PsiF_finK P μ fd σ ρp X).trans
      (sep_congr
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (Equiv.refl _)))
    (fun X Y h => PsiF_mono P μ fd σ ρp h)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k pre x hk hlen hnok
      show x ∈ bigPF P μ fd σ ρp (fd.ctors.get j).1 k pre
      exact hnok
    · intro k pre pre' hk hlen hlen' hle
      exact bigPF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .plain from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk hlen
      show Equiv (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
        ((semF P μ fd σ ρp (fd.ctors.get j).1).domBig k pre)
      exact Equiv.rfl
    · intro k pre pre' hk hlen hlen' hle
      exact domBigF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .fn from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk
      show Equiv (lift.{1, 4} (singleton pempty)) (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
      rw [domBigF_direct P μ fd σ ρp (fd.ctors.get j).1 k pre
        (kindsOf_getElem? hk).2]
      exact (lift_singleton_equiv.{1, 4} pempty).trans
        (singleton_congr (lift_pempty_equiv.{1, 4}))
  · intro j X xs hIn
    exact hcovF P μ fd σ ρp (fd.ctors.get j).1
      (hW ▸ mem_univIn.{1, 4}.mpr (small_lift.{1, 4} X)) j.val xs hIn

/-- `Small` from `W4`-membership under the `W4 kk = univIn` identification. -/
theorem small_of_mem_W4_2 (fd : FamData) {σ : Nat → Nat}
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{2, 4}) {x : PSet.{4}}
    (h : x ∈ W4 (evalTotal σ fd.resLevel)) : Small.{2, 4} x := by
  rw [hW] at h
  exact mem_univIn.{2, 4}.mp h

/-- The `u = 2` `BigDoms` for a constructor's field list. -/
noncomputable def bigDomsF2 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (hW : W4 (evalTotal σ fd.resLevel) = univIn.{2, 4}) :
    BigDoms.{2, 4} where
  kinds := kindsOf fd.fref Fs
  bigP := bigPF P μ fd σ ρp Fs
  bigR := domBigF P μ fd σ ρp Fs
  smallP := fun k pre => small_of_mem_W4_2 fd hW (bigPF_mem_W4 P μ fd σ ρp Fs k pre)
  smallR := fun k pre => small_of_mem_W4_2 fd hW (domBigF_mem_W4 P μ fd σ ρp Fs k pre)

/-- The guarded signature of the `u = 2` family packaging. -/
noncomputable def sigF2 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{2, 4}) : GSig.{2} :=
  sigOfBig.{2, 4} P.c2
    (fun j : Fin fd.ctors.length => bigDomsF2 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1)

/-- `lift (gSet (sigF2 …))` is the least fixed point of `PsiF`, and it is a
member of the `W4` bound. -/
theorem lfpF2 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{2, 4})
    (hN : ∀ j : Fin fd.ctors.length,
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    IsLfp (PsiF P μ fd σ ρp) (lift.{2, 4} (gSet (sigF2 P μ fd σ ρp hW))) ∧
      lift.{2, 4} (gSet (sigF2 P μ fd σ ρp hW)) ∈ W4 (evalTotal σ fd.resLevel) := by
  refine ⟨?_, hW ▸ mem_univIn.{2, 4}.mpr (small_lift.{2, 4} _)⟩
  refine lfp_of_big.{2, 4} P.c2
    (fun j : Fin fd.ctors.length => bigDomsF2 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1) ?_ (W4 (evalTotal σ fd.resLevel)) ?_
    (PsiF P μ fd σ ρp) (fun X => (PsiF_finK P μ fd σ ρp X).trans
      (sep_congr
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (Equiv.refl _)))
    (fun X Y h => PsiF_mono P μ fd σ ρp h)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k pre x hk hlen hnok
      show x ∈ bigPF P μ fd σ ρp (fd.ctors.get j).1 k pre
      exact hnok
    · intro k pre pre' hk hlen hlen' hle
      exact bigPF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .plain from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk hlen
      show Equiv (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
        ((semF P μ fd σ ρp (fd.ctors.get j).1).domBig k pre)
      exact Equiv.rfl
    · intro k pre pre' hk hlen hlen' hle
      exact domBigF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .fn from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk
      show Equiv (lift.{2, 4} (singleton pempty)) (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
      rw [domBigF_direct P μ fd σ ρp (fd.ctors.get j).1 k pre
        (kindsOf_getElem? hk).2]
      exact (lift_singleton_equiv.{2, 4} pempty).trans
        (singleton_congr (lift_pempty_equiv.{2, 4}))
  · intro j X xs hIn
    exact hcovF P μ fd σ ρp (fd.ctors.get j).1
      (hW ▸ mem_univIn.{2, 4}.mpr (small_lift.{2, 4} X)) j.val xs hIn

/-- `Small` from `W4`-membership under the `W4 kk = univIn` identification. -/
theorem small_of_mem_W4_3 (fd : FamData) {σ : Nat → Nat}
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{3, 4}) {x : PSet.{4}}
    (h : x ∈ W4 (evalTotal σ fd.resLevel)) : Small.{3, 4} x := by
  rw [hW] at h
  exact mem_univIn.{3, 4}.mp h

/-- The `u = 3` `BigDoms` for a constructor's field list. -/
noncomputable def bigDomsF3 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (hW : W4 (evalTotal σ fd.resLevel) = univIn.{3, 4}) :
    BigDoms.{3, 4} where
  kinds := kindsOf fd.fref Fs
  bigP := bigPF P μ fd σ ρp Fs
  bigR := domBigF P μ fd σ ρp Fs
  smallP := fun k pre => small_of_mem_W4_3 fd hW (bigPF_mem_W4 P μ fd σ ρp Fs k pre)
  smallR := fun k pre => small_of_mem_W4_3 fd hW (domBigF_mem_W4 P μ fd σ ρp Fs k pre)

/-- The guarded signature of the `u = 3` family packaging. -/
noncomputable def sigF3 (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{3, 4}) : GSig.{3} :=
  sigOfBig.{3, 4} P.c3
    (fun j : Fin fd.ctors.length => bigDomsF3 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1)

/-- `lift (gSet (sigF3 …))` is the least fixed point of `PsiF`, and it is a
member of the `W4` bound. -/
theorem lfpF3 (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (hW : W4 (evalTotal σ fd.resLevel) = univIn.{3, 4})
    (hN : ∀ j : Fin fd.ctors.length,
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    IsLfp (PsiF P μ fd σ ρp) (lift.{3, 4} (gSet (sigF3 P μ fd σ ρp hW))) ∧
      lift.{3, 4} (gSet (sigF3 P μ fd σ ρp hW)) ∈ W4 (evalTotal σ fd.resLevel) := by
  refine ⟨?_, hW ▸ mem_univIn.{3, 4}.mpr (small_lift.{3, 4} _)⟩
  refine lfp_of_big.{3, 4} P.c3
    (fun j : Fin fd.ctors.length => bigDomsF3 P μ fd σ ρp (fd.ctors.get j).1 hW)
    (fun j => semF P μ fd σ ρp (fd.ctors.get j).1) ?_ (W4 (evalTotal σ fd.resLevel)) ?_
    (PsiF P μ fd σ ρp) (fun X => (PsiF_finK P μ fd σ ρp X).trans
      (sep_congr
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (fun a b hab ⟨j, xs, hz, hIn⟩ => ⟨j, xs, hab.symm.trans hz, hIn⟩)
        (Equiv.refl _)))
    (fun X Y h => PsiF_mono P μ fd σ ρp h)
  · intro j
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro k pre x hk hlen hnok
      show x ∈ bigPF P μ fd σ ρp (fd.ctors.get j).1 k pre
      exact hnok
    · intro k pre pre' hk hlen hlen' hle
      exact bigPF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .plain from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk hlen
      show Equiv (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
        ((semF P μ fd σ ρp (fd.ctors.get j).1).domBig k pre)
      exact Equiv.rfl
    · intro k pre pre' hk hlen hlen' hle
      exact domBigF_loc P μ fd σ ρp (hN j)
        (show (kindsOf fd.fref (fd.ctors.get j).1)[k]? = some .fn from hk) hlen hlen'
        (show LEq (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre)
          (plainVals ((kindsOf fd.fref (fd.ctors.get j).1).take k) pre') from hle)
    · intro k pre hk
      show Equiv (lift.{3, 4} (singleton pempty)) (domBigF P μ fd σ ρp (fd.ctors.get j).1 k pre)
      rw [domBigF_direct P μ fd σ ρp (fd.ctors.get j).1 k pre
        (kindsOf_getElem? hk).2]
      exact (lift_singleton_equiv.{3, 4} pempty).trans
        (singleton_congr (lift_pempty_equiv.{3, 4}))
  · intro j X xs hIn
    exact hcovF P μ fd σ ρp (fd.ctors.get j).1
      (hW ▸ mem_univIn.{3, 4}.mpr (small_lift.{3, 4} X)) j.val xs hIn

/-- `W4` at the small-stage indices is the corresponding `univIn`. -/
theorem W4_eq_1 : W4 1 = univIn.{0, 4} := rfl
/-- `W4 2 = univIn`. -/
theorem W4_eq_2 : W4 2 = univIn.{1, 4} := rfl
/-- `W4 3 = univIn`. -/
theorem W4_eq_3 : W4 3 = univIn.{2, 4} := rfl
/-- `W4 (k + 4) = univIn`. -/
theorem W4_eq_add4 (k : Nat) : W4 (k + 4) = univIn.{3, 4} := rfl

/-- The dispatched least fixed point of `PsiF`: pick the `u`-instance matching
the family result level. -/
noncomputable def DStar (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (σ : Nat → Nat) (ρp : Nat → PSet.{4}) : PSet.{4} :=
  match h : evalTotal σ fd.resLevel with
  | 0 => pempty
  | 1 => lift.{0, 4} (gSet (sigF0 P μ fd σ ρp (by rw [h]; exact W4_eq_1)))
  | 2 => lift.{1, 4} (gSet (sigF1 P μ fd σ ρp (by rw [h]; exact W4_eq_2)))
  | 3 => lift.{2, 4} (gSet (sigF2 P μ fd σ ρp (by rw [h]; exact W4_eq_3)))
  | k + 4 => lift.{3, 4} (gSet (sigF3 P μ fd σ ρp (by rw [h]; exact W4_eq_add4 k)))

/-- `DStar` is the least fixed point of `PsiF` and lies in the `W4` bound. -/
theorem DStar_lfp (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel ≠ 0)
    (hN : ∀ j : Fin fd.ctors.length,
      NonIRSem P μ σ ρp fd.fref (fd.ctors.get j).1) :
    IsLfp (PsiF P μ fd σ ρp) (DStar P μ fd σ ρp) ∧
      DStar P μ fd σ ρp ∈ W4 (evalTotal σ fd.resLevel) := by
  unfold DStar
  split
  · rename_i h; exact absurd h hk
  · rename_i h
    exact lfpF0 P μ fd σ ρp (by rw [h]; exact W4_eq_1) hN
  · rename_i h
    exact lfpF1 P μ fd σ ρp (by rw [h]; exact W4_eq_2) hN
  · rename_i h
    exact lfpF2 P μ fd σ ρp (by rw [h]; exact W4_eq_3) hN
  · rename_i h
    exact lfpF3 P μ fd σ ρp (by rw [h]; exact W4_eq_add4 _) hN

/-- At level `0`, `DStar` is empty. -/
theorem DStar_zero (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
    (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (hk : evalTotal σ fd.resLevel = 0) :
    DStar P μ fd σ ρp = pempty := by
  unfold DStar
  split
  · rfl
  · rename_i h; exact absurd h (by rw [hk]; decide)
  · rename_i h; exact absurd h (by rw [hk]; decide)
  · rename_i h; exact absurd h (by rw [hk]; decide)
  · rename_i h; rw [hk] at h; exact Nat.noConfusion h

end PSet

end Rcic.F3
