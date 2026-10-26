import rcic.RcicF3KTWFamOp

/-!
# F3 S7 KT-2b-4a: least fixed points and stage closure

Generic `IsLfp` facts, the finite-sum form of `iUnionT` over `phiK`, stage
closure of fitting tuples, and the `Fin`-form of `PsiF`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

universe u v w T

namespace PSet

open Rcic.Declarative

/-- A least fixed point: pre-fixed, post-fixed, and least among closed sets. -/
def IsLfp (Ψ : PSet.{T} → PSet.{T}) (Y : PSet.{T}) : Prop :=
  Sub (Ψ Y) Y ∧ Sub Y (Ψ Y) ∧ ∀ Z, Sub (Ψ Z) Z → Sub Y Z

/-- Least fixed points of `≈`-equal operators are `≈`-equal. -/
theorem IsLfp.unique_of_congr {Ψ Ψ' : PSet.{T} → PSet.{T}} {Y Y' : PSet.{T}}
    (hΨ : ∀ X, Equiv (Ψ X) (Ψ' X)) (h : IsLfp Ψ Y) (h' : IsLfp Ψ' Y') :
    Equiv Y Y' :=
  ext fun z =>
    ⟨fun hz => h.2.2 Y' (fun w hw => h'.1 w (mem_congr_right (hΨ Y') hw)) z hz,
     fun hz => h'.2.2 Y (fun w hw => h.1 w (mem_congr_right (hΨ Y).symm hw)) z hz⟩

/-- `lift (gSet S)` is the least fixed point of a W-shaped operator. -/
theorem IsLfp.of_wshaped {Φ : PSet.{max u v} → PSet.{max u v}} {S : GSig.{u}}
    (hW : WShaped.{u, v} Φ S)
    (hmono : ∀ X Y, Sub X Y → Sub (Φ X) (Φ Y)) : IsLfp Φ (lift.{u, v} (gSet S)) :=
  ⟨fun z hz => mem_congr_right (lift_gSet_fixed hW) hz,
   fun z hz => mem_congr_right (lift_gSet_fixed hW).symm hz,
   fun Z hZ => lift_gSet_least hW hmono hZ⟩

/-- `WShaped` transports along a pointwise `≈` of the operator. -/
theorem wshaped_congr {Φ Φ' : PSet.{max u v} → PSet.{max u v}} {S : GSig.{u}}
    (h : ∀ X, Equiv (Φ X) (Φ' X)) (hW : WShaped.{u, v} Φ S) : WShaped.{u, v} Φ' S :=
  ⟨fun X => (h (lift.{u, v} X)).symm.trans (hW.at_lift X)⟩

/-- The `iUnionT` over `Fin n` many `phiK`s is the `Fin`-indexed constructor sum. -/
theorem iUnionT_phiK_fin {n : Nat} (kinds : Fin n → List PKind)
    (Sm : Fin n → Sem.{max u v}) (B X : PSet.{max u v}) :
    Equiv (iUnionT.{u, v}
        (fun j : ULift.{u} (Fin n) => phiK j.down.val (kinds j.down) (Sm j.down) B X))
      (sep (fun z => ∃ j : Fin n, ∃ xs, Equiv z (dataVal j.val xs) ∧
          (Sm j).InPhi X (kinds j) xs 0 []) B) := by
  apply ext; intro z; constructor
  · intro hz
    obtain ⟨j, hz⟩ := mem_iUnionT.mp hz
    obtain ⟨i, ⟨xs, he, hIn⟩, hiz⟩ := mem_sep.mp hz
    exact mem_sep.mpr ⟨i, ⟨j.down, xs, he, hIn⟩, hiz⟩
  · intro hz
    obtain ⟨i, ⟨j, xs, he, hIn⟩, hiz⟩ := mem_sep.mp hz
    exact mem_iUnionT.mpr ⟨ULift.up j, mem_sep.mpr ⟨i, ⟨xs, he, hIn⟩, hiz⟩⟩

/-- `tup` of stage members is a stage member. -/
theorem tup_mem_stage {W : PSet.{T}} (hW : Stage W) :
    ∀ (xs : List PSet.{T}), (∀ x, x ∈ xs → x ∈ W) → tup xs ∈ W
  | [], _ => hW.empty
  | x :: xs, h =>
      hW.pair (hW.singleton_mem (h x (List.mem_cons_self _ _)))
        (hW.pair (h x (List.mem_cons_self _ _))
          (tup_mem_stage hW xs (fun y hy => h y (List.mem_cons_of_mem _ hy))))

/-- A data value built from stage members is a stage member. -/
theorem dataVal_mem_stage {W : PSet.{T}} (hW : Stage W) (j : Nat)
    (xs : List PSet.{T}) (h : ∀ x, x ∈ xs → x ∈ W) : dataVal j xs ∈ W := by
  show pair (singleton pempty) (pair pempty (ordPair (ord j) (tup xs))) ∈ W
  exact hW.pair (hW.singleton_mem hW.empty) (hW.pair hW.empty
    (hW.pair (hW.singleton_mem (ord_mem_stage hW j))
      (hW.pair (ord_mem_stage hW j) (tup_mem_stage hW xs h))))

/-- `Sem.InPhi`-fitting tuples are stage members, given the guard closures. -/
theorem InPhi_mem_stage {W : PSet.{w}} (hW : Stage W) (Sm : Sem.{w}) {X : PSet.{w}}
    (hX : X ∈ W)
    (hP : ∀ k pre x, Sm.nonrecOk k pre x → x ∈ W)
    (hR : ∀ k pre, Sm.domBig k pre ∈ W) :
    ∀ (ps : List PKind) (xs : List PSet.{w}) (k : Nat) (pre : List PSet.{w}),
      Sm.InPhi X ps xs k pre → ∀ x, x ∈ xs → x ∈ W
  | [], xs, _, _, hIn => by
      cases xs with
      | nil => intro x hx; exact (List.not_mem_nil x hx).elim
      | cons x xs' => exact False.elim hIn
  | .plain :: ps, x :: xs, k, pre, ⟨hx, hin⟩ => fun y hy =>
      (List.mem_cons.mp hy).elim (fun e => e ▸ hP k pre x hx)
        (fun hy' => InPhi_mem_stage hW Sm hX hP hR ps xs (k + 1) (pre ++ [x]) hin y hy')
  | .direct :: ps, x :: xs, k, pre, ⟨⟨hxm, _⟩, hin⟩ => fun y hy =>
      (List.mem_cons.mp hy).elim (fun e => e ▸ hW.trans hX hxm)
        (fun hy' => InPhi_mem_stage hW Sm hX hP hR ps xs (k + 1) (pre ++ [x]) hin y hy')
  | .fn :: ps, x :: xs, k, pre, ⟨hxm, hin⟩ => fun y hy =>
      (List.mem_cons.mp hy).elim (fun e => e ▸ hW.trans
          (hW.pi (fun y y' hy' => Sem.fib_resp Sm X k pre hy') (hR k pre)
            (fun y hy => hW.subset hX (fun z hz => mem_sep_subset hz))) hxm)
        (fun hy' => InPhi_mem_stage hW Sm hX hP hR ps xs (k + 1) (pre ++ [x]) hin y hy')
  | p :: _, [], _, _, _ => fun x hx => (List.not_mem_nil x hx).elim

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)

/-- `PsiF` in `Fin`-indexed constructor form. -/
theorem PsiF_fin (σ : Nat → Nat) (ρp : Nat → PSet.{4}) (X : PSet.{4}) :
    Equiv (PsiF P μ fd σ ρp X)
      (sep (fun z => ∃ j : Fin fd.ctors.length, ∃ xs, Equiv z (dataVal j.val xs) ∧
          Sem.InPhi (semF P μ fd σ ρp (fd.ctors.get j).1) X
            (kindsOf fd.fref (fd.ctors.get j).1) xs 0 [])
        (W4 (evalTotal σ fd.resLevel))) := by
  unfold PsiF
  apply sep_congr _ _ Equiv.rfl
  · intro a b hab ⟨j, c, xs, hcj, hia, hIn⟩
    obtain ⟨hlt, hc⟩ := List.getElem?_eq_some.mp hcj
    have hgc : fd.ctors.get ⟨j, hlt⟩ = c := hc
    exact ⟨⟨j, hlt⟩, xs, hab.symm.trans hia, hgc ▸ hIn⟩
  · intro a b hab ⟨j, xs, hia, hIn⟩
    exact ⟨j.val, fd.ctors.get j, xs,
      List.getElem?_eq_getElem j.isLt, hab.symm.trans hia, hIn⟩


/-- The spine arguments of a bounded expression are bounded. -/
theorem exprLevelsBounded_appsSpine_args {k : Nat} :
    ∀ (A : Expr Nat), exprLevelsBounded k A = true → ExprsBounded k (appsSpine A).2
  | .app f x, h => by
      rw [exprLevelsBounded, Bool.and_eq_true] at h
      exact fun e he => (List.mem_append.mp he).elim
        (fun hef => exprLevelsBounded_appsSpine_args f h.1 e hef)
        (fun hex => by obtain rfl := List.mem_singleton.mp hex; exact h.2)
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .pi _ _, _ |
      .letE _ _ _, _ | .lit _, _ =>
      fun e he => absurd he (List.not_mem_nil e)

/-- The family-index part of a bounded recursive occurrence is bounded. -/
theorem exprLevelsBounded_familyIdx {k np : Nat} {A : Expr Nat}
    (h : exprLevelsBounded k A = true) : ExprsBounded k (familyIdx np A) :=
  fun e he => exprLevelsBounded_appsSpine_args A h e (List.mem_of_mem_drop he)

/-- The pi-domain of a bounded expression is bounded. -/
theorem exprLevelsBounded_piDom {k : Nat} {A : Expr Nat}
    (h : exprLevelsBounded k A = true) : exprLevelsBounded k (piDom A) = true := by
  cases A <;> try exact h
  rename_i a b
  show exprLevelsBounded k a = true
  rw [exprLevelsBounded, Bool.and_eq_true] at h
  exact h.1

/-- The pi-codomain of a bounded expression is bounded. -/
theorem exprLevelsBounded_piCod {k : Nat} {A : Expr Nat}
    (h : exprLevelsBounded k A = true) : exprLevelsBounded k (piCod A) = true := by
  cases A <;> try exact h
  rename_i a b
  show exprLevelsBounded k b = true
  rw [exprLevelsBounded, Bool.and_eq_true] at h
  exact h.2

/-- A bounded field list gives bounded `fieldAt` values (default is bounded). -/
theorem fieldAt_bounded {k : Nat} {Fs : List (Expr Nat)} (hFs : ExprsBounded k Fs)
    (i : Nat) : exprLevelsBounded k (fieldAt Fs i) = true := by
  show exprLevelsBounded k (Fs.getD i (.sort .zero)) = true
  unfold List.getD
  cases h : Fs.get? i with
  | none => rfl
  | some e => exact hFs e (List.getElem?_mem ((List.get?_eq_getElem? Fs i) ▸ h))

section

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) (fd : FamData)
variable {ar : Nat} {σ σ' : Nat → Nat}

/-- `nonrecOkF` puts the field value in the stage bound. -/
theorem nonrecOkF_mem_W4 (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) (x : PSet.{4})
    (h : nonrecOkF P μ fd σ ρp Fs k pre x) : x ∈ W4 (evalTotal σ fd.resLevel) :=
  truncW_mem_W4 P h

/-- `domBigF` is always a stage member (the `∈ W4` arm or `{∅}`). -/
theorem domBigF_mem_W4 (σ : Nat → Nat) (ρp : Nat → PSet.{4})
    (Fs : List (Expr Nat)) (k : Nat) (pre : List PSet.{4}) :
    domBigF P μ fd σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel) := by
  unfold domBigF
  split
  · unfold cond
    cases hdec : P.dec (domEF P μ σ ρp Fs k pre ∈ W4 (evalTotal σ fd.resLevel)) with
    | isTrue hE => exact hE
    | isFalse _ => exact (stageW4 P _).singleton_mem (stageW4 P _).empty
  · exact (stageW4 P _).singleton_mem (stageW4 P _).empty

/-- `argsFitF` only reads the level valuation below `ar`. -/
theorem argsFitF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    {A : Expr Nat} (hA : exprLevelsBounded ar A = true) (ρ : Nat → PSet.{4}) :
    argsFitF P μ fd σ ρ A ↔ argsFitF P μ fd σ' ρ A := by
  show TelFits (mkM P μ) σ (fd.params ++ fd.indices) ρ0
      ((appsSpine A).2.map (den (mkM P μ) σ ρ)) ↔ _
  rw [map_den_levels (mkM P μ) hσ ((appsSpine A).2)
    (exprLevelsBounded_appsSpine_args A hA) ρ]
  exact TelFits_levels (mkM P μ) hσ (fd.params ++ fd.indices) (hpi_of fd ar hB) ρ0
    ((appsSpine A).2.map (den (mkM P μ) σ' ρ))

/-- `recTupAt` only reads the level valuation below `ar`. -/
theorem recTupAt_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    {A : Expr Nat} (hA : exprLevelsBounded ar A = true) (ρ : Nat → PSet.{4}) :
    Equiv (recTupAt P μ fd σ ρ A) (recTupAt P μ fd σ' ρ A) := by
  unfold recTupAt
  rw [map_den_levels (mkM P μ) hσ (familyIdx fd.params.length A)
    (exprLevelsBounded_familyIdx hA) ρ]
  exact cond_congr (argsFitF_levels P μ fd hB hσ hA ρ) Equiv.rfl Equiv.rfl

/-- `nonrecOkF` only reads the level valuation below `ar`. -/
theorem nonrecOkF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat))
    (hFs : ExprsBounded ar Fs) (k : Nat) (pre : List PSet.{4}) (x : PSet.{4}) :
    nonrecOkF P μ fd σ ρp Fs k pre x ↔ nonrecOkF P μ fd σ' ρp Fs k pre x := by
  unfold nonrecOkF
  rw [evalTotal_agree hσ fd.resLevel hB.res,
    den_levels_agree (mkM P μ) hσ _ (fieldAt_bounded hFs k) (push pre ρp)]

/-- `domEF` only reads the level valuation below `ar`. -/
theorem domEF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat))
    (hFs : ExprsBounded ar Fs) (k : Nat) (pre : List PSet.{4}) :
    Equiv (domEF P μ σ ρp Fs k pre) (domEF P μ σ' ρp Fs k pre) := by
  unfold domEF
  rw [den_levels_agree (mkM P μ) hσ _
    (exprLevelsBounded_piDom (fieldAt_bounded hFs k)) (push pre ρp)]
  exact Equiv.rfl

/-- `domBigF` only reads the level valuation below `ar`. -/
theorem domBigF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat))
    (hFs : ExprsBounded ar Fs) (k : Nat) (pre : List PSet.{4}) :
    Equiv (domBigF P μ fd σ ρp Fs k pre) (domBigF P μ fd σ' ρp Fs k pre) := by
  unfold domBigF
  rw [evalTotal_agree hσ fd.resLevel hB.res]
  split
  · exact cond_congr
      ⟨fun hm => mem_congr_left (domEF_levels P μ fd hB hσ ρp Fs hFs k pre) hm,
        fun hm => mem_congr_left (domEF_levels P μ fd hB hσ ρp Fs hFs k pre).symm hm⟩
      (domEF_levels P μ fd hB hσ ρp Fs hFs k pre) Equiv.rfl
  · exact Equiv.rfl

/-- `recTupF` only reads the level valuation below `ar`. -/
theorem recTupF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) (Fs : List (Expr Nat))
    (hFs : ExprsBounded ar Fs) (k : Nat) (pre : List PSet.{4}) (y : PSet.{4}) :
    Equiv (recTupF P μ fd σ ρp Fs k pre y) (recTupF P μ fd σ' ρp Fs k pre y) := by
  unfold recTupF
  rw [evalTotal_agree hσ fd.resLevel hB.res]
  split
  · exact cond_congr
      ⟨fun hm => mem_congr_left (domEF_levels P μ fd hB hσ ρp Fs hFs k pre) hm,
        fun hm => mem_congr_left (domEF_levels P μ fd hB hσ ρp Fs hFs k pre).symm hm⟩
      (recTupAt_levels P μ fd hB hσ (exprLevelsBounded_piCod (fieldAt_bounded hFs k))
        (vcons y (push pre ρp))) Equiv.rfl
  · exact recTupAt_levels P μ fd hB hσ (fieldAt_bounded hFs k) (push pre ρp)

/-- `Sem.InPhi` at `semF` only reads the level valuation below `ar`. -/
theorem InPhi_semF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) {Fs : List (Expr Nat)}
    (hFs : ExprsBounded ar Fs) (X : PSet.{4}) :
    ∀ (ps : List PKind) (xs : List PSet.{4}) (k : Nat) (pre : List PSet.{4}),
      Sem.InPhi (semF P μ fd σ ρp Fs) X ps xs k pre →
        Sem.InPhi (semF P μ fd σ' ρp Fs) X ps xs k pre
  | [], xs, _, _, hIn => by
      cases xs with
      | nil => exact hIn
      | cons x xs' => exact hIn
  | .plain :: ps, x :: xs, k, pre, ⟨hx, hin⟩ =>
      ⟨(nonrecOkF_levels P μ fd hB hσ ρp Fs hFs k pre x).1 hx,
        InPhi_semF_levels hB hσ ρp hFs X ps xs (k + 1) (pre ++ [x]) hin⟩
  | .direct :: ps, x :: xs, k, pre, ⟨⟨hxm, hxe⟩, hin⟩ =>
      ⟨⟨hxm, ((resTupF_levels P μ fd hB hσ ρp x).symm.trans hxe).trans
          (recTupF_levels P μ fd hB hσ ρp Fs hFs k pre pempty)⟩,
        InPhi_semF_levels hB hσ ρp hFs X ps xs (k + 1) (pre ++ [x]) hin⟩
  | .fn :: ps, x :: xs, k, pre, ⟨hxm, hin⟩ =>
      ⟨mem_piSet_of_dep
        (fun y y' hy => Sem.fib_resp (semF P μ fd σ' ρp Fs) X k pre hy)
        (isFuncOnDep_equiv (domBigF_levels P μ fd hB hσ ρp Fs hFs k pre)
          (fun y y' hy => sep_congr
            (fun a b hab hb =>
              ((resTupF_levels P μ fd hB hσ ρp b).symm.trans
                ((resTupF_congr P μ fd σ ρp hab.symm).trans hb)).trans
                ((recTupF_levels P μ fd hB hσ ρp Fs hFs k pre y).trans
                  (recTupF_congr P μ fd σ' ρp Fs k (LEq.refl pre) hy)))
            (fun a b hab hb =>
              ((resTupF_levels P μ fd hB hσ ρp b).trans
                ((resTupF_congr P μ fd σ' ρp hab.symm).trans hb)).trans
                ((recTupF_levels P μ fd (σ := σ') (σ' := σ) hB (fun i hi => (hσ i hi).symm) ρp Fs hFs k pre y').trans
                  (recTupF_congr P μ fd σ ρp Fs k (LEq.refl pre) hy.symm)))
            (Equiv.refl X))
          (Equiv.refl x)
          (isFuncOnDep_of_mem_piSet
            (fun y y' hy => Sem.fib_resp (semF P μ fd σ ρp Fs) X k pre hy) hxm)),
        InPhi_semF_levels hB hσ ρp hFs X ps xs (k + 1) (pre ++ [x]) hin⟩
  | p :: ps, [], _, _, hIn => by cases p <;> exact hIn

/-- `PsiF` only reads the level valuation below `ar`. -/
theorem PsiF_levels (hB : FamBounded fd ar) (hσ : ∀ i, i < ar → σ i = σ' i)
    (ρp : Nat → PSet.{4}) (X : PSet.{4}) :
    Equiv (PsiF P μ fd σ ρp X) (PsiF P μ fd σ' ρp X) := by
  unfold PsiF
  rw [evalTotal_agree hσ fd.resLevel hB.res]
  exact sep_congr
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_levels P μ fd hB hσ ρp (hB.ctors c (List.getElem?_mem hcj)).1 X
        (kindsOf fd.fref c.1) xs 0 [] hIn⟩)
    (fun a b hab ⟨j, c, xs, hcj, hia, hIn⟩ => ⟨j, c, xs, hcj, hab.symm.trans hia,
      InPhi_semF_levels P μ fd (σ := σ') (σ' := σ) hB (fun i hi => (hσ i hi).symm) ρp
        (hB.ctors c (List.getElem?_mem hcj)).1 X
        (kindsOf fd.fref c.1) xs 0 [] hIn⟩)
    Equiv.rfl

end

end

end PSet

end Rcic.F3
