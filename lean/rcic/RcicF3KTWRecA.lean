import rcic.RcicF3KTWMinorA

/-!
# F3 class A KT-4b: `ihAt`/`ihChild` lemmas for Π-recursive fields

At a functional member of a denoted Π, `ihAt`'s raw-`mkLam` branch is `≈` the
interpretation's `lamVal` (modulo the non-`pi` codomain unfolding `ihAt` to `g`),
and `fapp`-applications on the graph's domain are transitive members of the
function graph itself — the `ihChild` content at Π fields.
-/

set_option autoImplicit false

universe u T

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- `condP` picks its first branch under `P`, up to `≈`. -/
theorem condP_equiv_pos {P : Prop} {a b : PSet.{u}} (h : P) : Equiv (condP P a b) a :=
  equiv_iff_mem.mpr fun z => by
    rw [mem_condP]
    exact ⟨fun hz => hz.elim (fun hz => hz.1) fun hz => absurd h hz.2,
      fun hz => Or.inl ⟨hz, h⟩⟩

/-- `condP` picks its second branch under `¬P`, up to `≈`. -/
theorem condP_equiv_neg {P : Prop} {a b : PSet.{u}} (h : ¬ P) : Equiv (condP P a b) b :=
  equiv_iff_mem.mpr fun z => by
    rw [mem_condP]
    exact ⟨fun hz => hz.elim (fun hz => absurd hz.2 h) fun hz => hz.1,
      fun hz => Or.inr ⟨hz, h⟩⟩

/-- At a functional member of a denoted Π, routec's λ-IH is the denotation's λ. -/
theorem ihAt_pi_equiv_lamVal (M : Interp.{T}) {A : PSet.{T}} {F : PSet.{T} → PSet.{T}}
    (hF : ∀ y y', Equiv y y' → Equiv (F y) (F y'))
    {x : PSet.{T}} (hx : x ∈ piSet (Ed M A) F) (g : PSet.{T} → PSet.{T})
    (hg : ∀ z z', Equiv z z' → Equiv (g z) (g z'))
    {D B : Expr Nat} (hB : ∀ D' B', B ≠ .pi D' B') :
    Equiv (ihAt g (.pi D B) x) (lamVal M A (fun y => g (fapp x y))) := by
  have hdom : Equiv (sImage pfst x) (Ed M A) := sImage_pfst_of_mem_piSet hF hx
  have hig : ∀ y, ihAt g B (fapp x y) = g (fapp x y) := fun y => by
    cases hB' : B with
    | pi D' B' => exact absurd hB' (hB D' B')
    | _ => rfl
  have hih : ihAt g (.pi D B) x =
      condP (∀ y, y ∈ sImage pfst x → Equiv (ihAt g B (fapp x y)) pempty)
        pempty (mkLam (fun y => ihAt g B (fapp x y)) (sImage pfst x)) := rfl
  have hlv : lamVal M A (fun y => g (fapp x y)) =
      cond M.dec (LamProof M A (fun y => g (fapp x y))) pempty
        (mkLam (fun y => g (fapp x y)) (Ed M A)) := rfl
  rw [hih, hlv]
  cases M.dec (LamProof M A (fun y => g (fapp x y))) with
  | isTrue h =>
      rw [cond_pos h]
      exact condP_equiv_pos fun y hy => by
        rw [hig]
        exact h y (mem_congr_right hdom hy)
  | isFalse h =>
      rw [cond_neg h]
      have hG : ¬ (∀ y, y ∈ sImage pfst x → Equiv (ihAt g B (fapp x y)) pempty) :=
        fun hG => h fun y hy => by
          show Equiv (g (fapp x y)) pempty
          rw [← hig]
          exact hG y (mem_congr_right hdom.symm hy)
      exact (condP_equiv_neg hG).trans
        (mkLam_congr' hdom fun a a' _ _ e => by
          show Equiv (ihAt g B (fapp x a)) (g (fapp x a'))
          rw [hig]
          exact hg _ _ (fapp_congr (Equiv.refl _) e))

/-- Members of a functional member of a data value are below it. -/
theorem memT_fapp_of_mem_piSet {Dm x : PSet.{T}} {F : PSet.{T} → PSet.{T}}
    (hF : ∀ y y', Equiv y y' → Equiv (F y) (F y'))
    (hx : x ∈ piSet Dm F) {y : PSet.{T}} (hy : y ∈ Dm) : MemT (fapp x y) x := by
  have hfun := isFuncOnDep_of_mem_piSet hF hx
  obtain ⟨b, _, hab⟩ := hfun.1 y hy
  have hfapp : Equiv (fapp x y) b := fapp_eq_of_uniq hfun.2.2 hab
  have e1 : fapp x y ∈ pair y b :=
    mem_congr_left hfapp.symm (mem_pair.mpr (Or.inr (Equiv.refl _)))
  have e2 : pair y b ∈ ordPair y b := mem_pair.mpr (Or.inr (Equiv.refl _))
  exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single e1) e2) hab

/-- `ihChild` at a Π field whose member is a functional graph. -/
theorem ihChild_pi_of_mem_piSet {z x : PSet.{T}} (hxz : MemT x z) {Dm : PSet.{T}}
    {F : PSet.{T} → PSet.{T}} (hF : ∀ y y', Equiv y y' → Equiv (F y) (F y'))
    (hx : x ∈ piSet Dm F) {D B : Expr Nat} (hB : ∀ D' B', B ≠ .pi D' B') :
    ihChild z (.pi D B) x := fun y hy =>
  have hdom : Equiv (sImage pfst x) Dm := sImage_pfst_of_mem_piSet hF hx
  ⟨Relation.TransGen.trans (memT_fapp_of_mem_piSet hF hx (mem_congr_right hdom hy)) hxz,
    by cases hB' : B with
    | pi D' B' => exact absurd hB' (hB D' B')
    | _ => trivial⟩

/-- Every Π-recursive field value is functional over its denoted domain. -/
def FnFunctional (M : Interp.{4}) (σ : Nat → Nat) (f : Nat) :
    List (Expr Nat) → (Nat → PSet.{4}) → List PSet.{4} → Prop
  | A :: As, ρ, x :: xs =>
      (kindOf f A = .fn → ∃ F : PSet.{4} → PSet.{4},
        (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
        x ∈ piSet (Ed M (den M σ ρ (piDom A))) F) ∧
        FnFunctional M σ f As (vcons x ρ) xs
  | _, _, _ => True

/-- At `FieldsClassA` fields the class-A λ-IH arguments agree componentwise
with routec's `ihArgs`: direct fields have `ihAt = g` (foldApps head, not `pi`),
and fn fields have `ihAt ≈ lamVal` at functional members. -/
theorem shArgsA_LEq_ihArgs (M : Interp.{4}) (σ : Nat → Nat) (f ar np nq : Nat)
    (g : PSet.{4} → PSet.{4}) (hg : ∀ z z', Equiv z z' → Equiv (g z) (g z')) :
    ∀ (Fs : List (Expr Nat)) (d : Nat) (ρ : Nat → PSet.{4}) (xs : List PSet.{4}),
      FieldsClassA f ar np nq Fs d → xs.length = Fs.length →
      FnFunctional M σ f Fs ρ xs →
      LEq (shArgsA M σ g (shapesOf f Fs) Fs ρ xs) (ihArgs f g Fs xs)
  | [], _, _, [], _, _, _ => trivial
  | A :: Fs, d, ρ, x :: xs, hcls, hxl, hfn => by
      obtain ⟨hdisj, hcls'⟩ := hcls
      obtain ⟨hF1, hF2⟩ := hfn
      have ih := shArgsA_LEq_ihArgs M σ f ar np nq g hg Fs (d + 1) (vcons x ρ) xs
        hcls' (Nat.succ.inj hxl) hF2
      rw [show shapesOf f (A :: Fs) = shapeOfKind (kindOf f A) ::
          shapesOf f Fs from rfl]
      rcases hdisj with h0 | hdir | hFn
      · rw [kindOf_free h0]
        show LEq (x :: shArgsA M σ g (shapesOf f Fs) Fs (vcons x ρ) xs)
            (ihArgs f g (A :: Fs) (x :: xs))
        unfold ihArgs
        rw [h0, if_neg (by decide)]
        exact ⟨Equiv.rfl, ih⟩
      · rw [kindOf_directRec hdir]
        obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
        have hocc : occursConst f A = true := by
          rw [hAe]
          exact occursConst_foldApps (e := .const f (canonL ar))
            (by simp [occursConst]) _
        show LEq (x :: g x :: shArgsA M σ g (shapesOf f Fs) Fs (vcons x ρ) xs)
            (ihArgs f g (A :: Fs) (x :: xs))
        unfold ihArgs
        rw [if_pos hocc]
        refine ⟨Equiv.rfl, ?_, ih⟩
        rw [hAe, ihAt_foldApps (fun _ _ h => Expr.noConfusion h)]
        exact Equiv.rfl
      · rw [kindOf_fnRec hFn]
        obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
        have hocc : occursConst f A = true := by
          rw [hA]
          simp only [occursConst, Bool.or_eq_true]
          exact Or.inr (occursConst_foldApps (e := .const f (canonL ar))
            (by simp [occursConst]) _)
        obtain ⟨F, hFe, hxF⟩ := hF1
          (kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩)
        show LEq (x :: lamVal M (den M σ ρ (piDom A)) (fun y => g (fapp x y)) ::
              shArgsA M σ g (shapesOf f Fs) Fs (vcons x ρ) xs)
            (ihArgs f g (A :: Fs) (x :: xs))
        unfold ihArgs
        rw [if_pos hocc]
        refine ⟨Equiv.rfl, ?_, ih⟩
        have hAx : ihAt g A x = ihAt g
            (.pi D' (foldApps (.const f (canonL ar))
              (policyParameterLocals np (d + 1) ++ idx))) x := by rw [hA]
        rw [hAx]
        exact (ihAt_pi_equiv_lamVal M hFe hxF g hg
          (foldApps_ne_pi (.const f (canonL ar))
            (fun _ _ h => Expr.noConfusion h)
            (policyParameterLocals np (d + 1) ++ idx))).symm
  | A :: _, _, _, [], _, hxl, _ => (Nat.succ_ne_zero _ hxl.symm).elim
  | [], _, _, _ :: _, _, hxl, _ => (Nat.succ_ne_zero _ hxl).elim

/-- `InPhi` over a candidate set gives `FnFunctional`: at a `.fn` field the
`InPhi` membership is a `piSet` member over `domBig`, which is the denoted
domain when it is in `W4` (and the fibre is total-contradictory otherwise). -/
theorem fnFunctional_of_InPhi (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (σ : Nat → Nat) (ps : List PSet.{4}) (Z : PSet.{4})
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest done.length →
      Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest) xs
        done.length pre →
      FnFunctional (mkM P μ) σ fd.fref rest (push pre (push ps ρ0)) xs := by
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
      cases xs with
      | nil =>
          exact Nat.noConfusion (Sem.InPhi.length _ _ _ _ _ hIn)
      | cons x xs' =>
          rcases hdisj with h0 | hdir | hFn
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_free h0] at hIn
            obtain ⟨hx, hin⟩ := hIn
            show (kindOf fd.fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) σ (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) σ fd.fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun h => ?_, ?_⟩
            · rw [kindOf_free h0] at h; cases h
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
          · simp only [kindsOf, List.map] at hIn
            rw [kindOf_directRec hdir] at hIn
            obtain ⟨⟨hxm, hxe⟩, hin⟩ := hIn
            show (kindOf fd.fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) σ (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) σ fd.fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun h => ?_, ?_⟩
            · rw [kindOf_directRec hdir] at h; cases h
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
          · simp only [kindsOf, List.map] at hIn
            obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            rw [kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩] at hIn
            obtain ⟨hxp, hin⟩ := hIn
            show (kindOf fd.fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) σ (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) σ fd.fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun _ => ?_, ?_⟩
            · cases hdec : P.dec (domEF P μ σ (push ps ρ0) Fs done.length pre ∈
                  W4 (evalTotal σ fd.resLevel)) with
              | isTrue hdW =>
                  have hdom : (semF P μ fd σ (push ps ρ0) Fs).domBig
                      done.length pre =
                      domEF P μ σ (push ps ρ0) Fs done.length pre := by
                    show domBigF P μ fd σ (push ps ρ0) Fs done.length pre = _
                    unfold domBigF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩,
                      cond_pos hdW]
                  have hxp' : x ∈ piSet
                      (domEF P μ σ (push ps ρ0) Fs done.length pre)
                      ((semF P μ fd σ (push ps ρ0) Fs).fib Z done.length pre) :=
                    mem_congr_right (piSet_congr (by rw [hdom]; exact Equiv.rfl)
                      (fun a a' h => Sem.fib_resp _ _ _ _ h)) hxp
                  have hdomE : domEF P μ σ (push ps ρ0) Fs done.length pre =
                      Ed (mkM P μ) (den (mkM P μ) σ (push pre (push ps ρ0))
                        (piDom A)) := by
                    unfold domEF
                    rw [hf]
                  rw [hdomE] at hxp'
                  exact ⟨fun y => (semF P μ fd σ (push ps ρ0) Fs).fib Z
                      done.length pre y,
                    fun y y' hy => Sem.fib_resp _ _ _ _ hy, hxp'⟩
              | isFalse hdW =>
                  exfalso
                  have hdom : (semF P μ fd σ (push ps ρ0) Fs).domBig
                      done.length pre = singleton pempty := by
                    show domBigF P μ fd σ (push ps ρ0) Fs done.length pre = _
                    unfold domBigF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩,
                      cond_neg hdW]
                  have hgd := isFuncOnDep_of_mem_piSet
                    (fun a a' h => Sem.fib_resp _ _ _ _ h)
                    (mem_congr_right (piSet_congr (by rw [hdom]; exact Equiv.rfl)
                      (fun a a' h => Sem.fib_resp _ _ _ _ h)) hxp)
                  obtain ⟨b, hb, -⟩ := hgd.1 pempty (mem_singleton.mpr Equiv.rfl)
                  obtain ⟨bi, hreT, -⟩ := mem_sep.mp hb
                  have hrecT : (semF P μ fd σ (push ps ρ0) Fs).recTup
                      done.length pre pempty = singleton pempty := by
                    show recTupF P μ fd σ (push ps ρ0) Fs
                        done.length pre pempty = _
                    unfold recTupF
                    rw [hf, kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩,
                      cond_neg hdW]
                  exact resTupF_ne_sentinel P μ fd σ (push ps ρ0) _
                    (hrecT ▸ hreT)
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH hin
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClassA fd.fref ar fd.params.length fd.indices.length rest'
          (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          FieldsClassA fd.fref ar fd.params.length fd.indices.length rest'
            done'.length →
          Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest') xs
            done'.length pre →
          FnFunctional (mkM P μ) σ fd.fref rest' (push pre (push ps ρ0)) xs)
        (hin : Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest')
          xs' (done.length + 1) (pre ++ [x])) :
        FnFunctional (mkM P μ) σ fd.fref rest'
          (vcons x (push pre (push ps ρ0))) xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x])
          (push ps ρ0) := by rw [push_append]; rfl
      rw [hvey]
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        (by rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton, hpre])
        (by rw [List.length_append]; exact hcls')
        (by rw [List.length_append]; exact hin)

/-- `FieldsClassA` premise from `RecGroupA`'s `fields` (already class-A). -/
theorem hclsA_of_recGroupA {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} (G : RecGroupA a) :
    ∀ c, c ∈ (famDataOf a).ctors →
      FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length c.1 0 := by
  intro c hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  show FieldsClassA _ _ _ _ (a.constructorViews i).fields 0
  exact G.fields i

/-- Constructor result-index expressions are family-free (from `RecGroupA`). -/
theorem hri_of_recGroupA {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} (G : RecGroupA a) :
    ∀ c, c ∈ (famDataOf a).ctors → ∀ e, e ∈ c.2 →
      occursConst (famDataOf a).fref e = false := by
  intro c hc e he
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  exact G.riFree i e he

/-- The family's entry is the family's value, at every recursor instance —
`famμ_of_KT` for `RecGroupA`. -/
theorem famμ_of_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs)) (G : RecGroupA a)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2) (vs : List Nat) :
    Equiv (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf a)) :=
  (hKT _).trans ((famKT_fix P μ (famDataOf a) a.family.member.arity hN G.bounded G.famFree
      (hclsA_of_recGroupA G) (hri_of_recGroupA G) (hres_of_admitted a) hf _).symm.trans
    ((famVal_levels (mkM P (tabKT P μ (famDataOf a)))
      (σOf_policyFamilyLevels_agree a.family vs) W4 _ G.bounded).trans
      (famVal_tables P (tabKT_equiv P μ a hKT) _ _)))

/-- A recursive occurrence at a nonzero result level reads the `DStar` fibre —
`ed_recOcc_KT` for `RecGroupA` (only `bounded`/`famFree` are used). -/
theorem ed_recOcc_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs)) (G : RecGroupA a)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (σ : Nat → Nat) (hk : evalTotal σ (famDataOf a).resLevel ≠ 0)
    (ps ys : List PSet.{4}) (hps : ps.length = (famDataOf a).params.length)
    (idx : List (Expr Nat)) (hidx : idx.length = (famDataOf a).indices.length)
    (hfree : ∀ e, e ∈ idx → occursConst (famDataOf a).fref e = false)
    (x : PSet.{4}) :
    x ∈ Ed (mkM P μ) (den (mkM P μ) σ (push ys (push ps ρ0))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) ↔
      x ∈ DStar P μ (famDataOf a) σ (push ps ρ0) ∧
        Equiv (resTupF P μ (famDataOf a) σ (push ps ρ0) x)
          (recTupAt P μ (famDataOf a) σ (push ys (push ps ρ0))
            (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
              (policyParameterLocals (famDataOf a).params.length ys.length ++ idx))) := by
  have hB : FamBounded (famDataOf a) a.family.member.arity := G.bounded
  have hpf : ∀ e, e ∈ (famDataOf a).params ++ (famDataOf a).indices →
      occursConst (famDataOf a).fref e = false := G.famFree
  let A := foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
    (policyParameterLocals (famDataOf a).params.length ys.length ++ idx)
  let ρ := push ys (push ps ρ0)
  let vs' := (canonL a.family.member.arity).map (evalTotal σ)
  have hagg := evalTotal_agree (σOf_canon σ a.family.member.arity)
    (famDataOf a).resLevel hB.res
  have hkk : evalTotal (σOf vs') (famDataOf a).resLevel ≠ 0 :=
    fun h0 => hk (hagg.symm.trans h0)
  have hX : famKT P μ (famDataOf a) vs' = famLfp P μ (famDataOf a) vs' := by
    unfold famKT
    rw [if_neg hkk]
  have hco : CanonOcc (famDataOf a).fref a.family.member.arity A :=
    canonOcc_foldApps _ (fun e he => by
      rcases List.mem_append.mp he with h | h
      · exact canonOcc_of_free
          (paramLocals_free (famDataOf a).fref (famDataOf a).params.length ys.length e h)
      · exact canonOcc_of_free (hfree e h))
  have deneq := den_transfer P μ (famDataOf a).fref a.family.member.arity σ hX hf A hco ρ
  have e1 := ed_recOcc P μ (famDataOf a) a.family.member.arity
    (DStar P μ (famDataOf a)) hB hpf
    (fun σ' ρ1 ρ' hρ => DStar_env P μ (famDataOf a) hN σ' hρ)
    (fun σ' σ'' hσ ρ1 => DStar_levels P μ (famDataOf a) a.family.member.arity hN hB hσ ρ1)
    (fun σ' ρ1 z hz => DStar_ne P μ (famDataOf a) hN σ' ρ1 z hz)
    (fun σ' ρ1 => DStar_mem P μ (famDataOf a) hN σ' ρ1)
    σ ps ys hps idx hidx hfree
  have e2 : Equiv (Ed (mkM P (tabKT P μ (famDataOf a)))
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A))
      (Ed (mkM P μ) (den (mkM P μ) σ ρ A)) :=
    Ed_dec_eq P (tabKT P μ (famDataOf a)) μ
      (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) ▸
      ed_congr (mkM P μ)
        (den_tables P (tabKT_equiv P μ a hKT) σ A (fun _ => Equiv.rfl))
  constructor
  · intro hx
    have hx1 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) :=
      mem_congr_right e2.symm hx
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a)))))
        (den (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a))))) σ ρ A) :=
      (Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))) σ ρ A)).symm ▸
        (deneq.symm ▸ hx1)
    obtain ⟨i, h1, h2⟩ := mem_sep.mp (mem_congr_right e1 hx2)
    exact ⟨⟨i, h2⟩, (resTupF_congr P μ (famDataOf a) σ (push ps ρ0) h2).symm.trans h1⟩
  · intro ⟨hd, he⟩
    obtain ⟨i, hxi⟩ := hd
    have hx : x ∈ sep (fun z => Equiv (resTupF P μ (famDataOf a) σ (push ps ρ0) z)
        (recTupAt P μ (famDataOf a) σ (push ys (push ps ρ0)) A))
        (DStar P μ (famDataOf a) σ (push ps ρ0)) :=
      mem_sep.mpr ⟨i, (resTupF_congr P μ (famDataOf a) σ (push ps ρ0) hxi).trans he, hxi⟩
    have hx2 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a)))))
        (den (mkM P (upd μ (famDataOf a).fref (famOfD P μ (famDataOf a) (DStar P μ (famDataOf a))))) σ ρ A) :=
      mem_congr_right e1.symm hx
    have hx1 : x ∈ Ed (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a))))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) :=
      Ed_dec_eq P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))
        (upd μ (famDataOf a).fref (famLfp P μ (famDataOf a)))
        (den (mkM P (upd μ (famDataOf a).fref (famKT P μ (famDataOf a)))) σ ρ A) ▸
        (deneq ▸ hx2)
    have hx3 : x ∈ Ed (mkM P (tabKT P μ (famDataOf a)))
        (den (mkM P (tabKT P μ (famDataOf a))) σ ρ A) := hx1
    exact mem_congr_right e2 hx3

/-- `ihChildL` for a class-A constructor's fields, from `InPhi` over a
candidate set: `.fn` fields' `ihChild` is `ihChild_pi_of_mem_piSet` (the
`InPhi` `piSet` membership supplies the functional graph), `.direct` fields
are foldApps-headed (vacuous), `.plain` fields fail the `occursConst` guard. -/
theorem ihChildL_of_InPhiA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    (fd : FamData) (ar : Nat) (σ : Nat → Nat) (ps : List PSet.{4}) (Z : PSet.{4})
    (Fs : List (Expr Nat)) {z : PSet.{4}} :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest →
      (∀ y, y ∈ xs → MemT y z) →
      FieldsClassA fd.fref ar fd.params.length fd.indices.length rest done.length →
      Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest) xs
        done.length pre →
      ihChildL fd.fref z rest xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hzm hcls hIn
      trivial
  | cons A rest' IH =>
      intro pre xs hFs hzm hcls hIn
      obtain ⟨hdisj, hcls'⟩ := hcls
      have hf : fieldAt Fs done.length = A := by
        rw [hFs]
        show (done ++ A :: rest').getD done.length _ = A
        simp only [List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero, Option.getD_some]
      cases xs with
      | nil => trivial
      | cons x xs' =>
          have hzm' : ∀ y, y ∈ xs' → MemT y z :=
            fun y hy => hzm y (List.mem_cons_of_mem x hy)
          have hxm : MemT x z := hzm x (List.mem_cons_self x xs')
          simp only [kindsOf, List.map] at hIn
          rcases hdisj with h0 | hdir | hFn
          · rw [kindOf_free h0] at hIn
            obtain ⟨hx, hin⟩ := hIn
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hocc] at h0; exact Bool.noConfusion h0
            · exact ih_step done A rest' pre x xs' hFs hzm' hcls' IH hin
          · rw [kindOf_directRec hdir] at hIn
            obtain ⟨⟨hxm2, hxe⟩, hin⟩ := hIn
            obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hAe]
              exact ihChild_foldApps z (fun _ _ h => Expr.noConfusion h) _ x
            · exact ih_step done A rest' pre x xs' hFs hzm' hcls' IH hin
          · obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            rw [kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩] at hIn
            obtain ⟨hxp, hin⟩ := hIn
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hA]
              exact ihChild_pi_of_mem_piSet hxm
                (fun a a' h => Sem.fib_resp _ _ _ _ h) hxp
                (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
            · exact ih_step done A rest' pre x xs' hFs hzm' hcls' IH hin
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest')
        (hzm' : ∀ y, y ∈ xs' → MemT y z)
        (hcls' : FieldsClassA fd.fref ar fd.params.length fd.indices.length rest'
          (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' →
          (∀ y, y ∈ xs → MemT y z) →
          FieldsClassA fd.fref ar fd.params.length fd.indices.length rest'
            done'.length →
          Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest') xs
            done'.length pre →
          ihChildL fd.fref z rest' xs)
        (hin : Sem.InPhi (semF P μ fd σ (push ps ρ0) Fs) Z (kindsOf fd.fref rest')
          xs' (done.length + 1) (pre ++ [x])) :
        ihChildL fd.fref z rest' xs' := by
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        hzm'
        (by rw [List.length_append]; exact hcls')
        (by rw [List.length_append]; exact hin)

/-- `DStar_motive` for class-A groups: every element of `DStar` satisfies the
motive condition, with `minor_ok_recA` + `IHOkA` for the Π-recursive fields
and the `shArgsA`/`ihArgs` bridge at the `recCore` call. -/
theorem DStar_motiveA
    (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length)
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
      have hclscA : FieldsClassA fd.fref a.family.member.arity fd.params.length
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
          σ ps hpsl c.1 hclscA xs).mpr hInD
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
        fun e he => canonOcc_fieldsClassA hclscA e he
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
      have hIn' : Sem.InPhi (semF P μ fd σ ρp
          ((a.constructorViews ⟨j, hjk⟩).fields)) Z
          (kindsOf fd.fref ((a.constructorViews ⟨j, hjk⟩).fields)) xs 0 [] := by
        have h := hIn
        rw [hcc] at h
        exact h
      have hih : IHOkA (mkM P μ) σ fd.params.length mo
          (recCore (mkM P μ) fd ms)
          (shapesOf fd.fref (ctorFieldsOf fd j)) (ctorFieldsOf fd j) ρp xs := by
        rw [hfo]
        exact ihOkA_of_InPhi P μ a vs ps mo (recCore (mkM P μ) fd ms) Z hZ hpsl
          ((a.constructorViews ⟨j, hjk⟩).fields) []
          ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
          (G.fields ⟨j, hjk⟩) hIn'
      have hmin := minor_ok_recA a G vs
        (famμ_of_KTA P μ a hKT G hN hf vs) hctorμ ps mo ms idxv hpsl hl hmo hms
        hfit j xs hcf (recCore (mkM P μ) fd ms) (recCore_resp _ _ _) hih
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
      have hch : ihChildL fd.fref (dataVal j xs) (ctorFieldsOf fd j) xs := by
        rw [hfo]
        exact ihChildL_of_InPhiA P μ fd a.family.member.arity σ ps Z
          ((a.constructorViews ⟨j, hjk⟩).fields) []
          ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl
          (fun y hy => memT_dataVal hy) (G.fields ⟨j, hjk⟩) hIn'
      have hrc : Equiv (recCore (mkM P μ) fd ms (dataVal j xs))
          (fapps (ms.getD j pempty)
            (ihArgs fd.fref (recCore (mkM P μ) fd ms) (ctorFieldsOf fd j) xs)) :=
        recCore_data _ _ _ Equiv.rfl hjk' hlen' hch
      have hxs' : xs.length = (ctorFieldsOf fd j).length := by
        rw [hfo]; rw [hcc] at hxs; exact hxs
      have hfnm : FnFunctional (mkM P μ) σ fd.fref (ctorFieldsOf fd j) ρp xs := by
        rw [hfo]
        exact fnFunctional_of_InPhi P μ fd a.family.member.arity σ ps Z
          ((a.constructorViews ⟨j, hjk⟩).fields) []
          ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
          (G.fields ⟨j, hjk⟩) hIn'
      have hclsA' : FieldsClassA fd.fref a.family.member.arity fd.params.length
          fd.indices.length (ctorFieldsOf fd j) 0 := by
        rw [hfo]; exact G.fields ⟨j, hjk⟩
      have hBridge : LEq (shArgsA (mkM P μ) σ (recCore (mkM P μ) fd ms)
            (shapesOf fd.fref (ctorFieldsOf fd j)) (ctorFieldsOf fd j) ρp xs)
          (ihArgs fd.fref (recCore (mkM P μ) fd ms) (ctorFieldsOf fd j) xs) :=
        shArgsA_LEq_ihArgs (mkM P μ) σ fd.fref a.family.member.arity
          fd.params.length fd.indices.length (recCore (mkM P μ) fd ms)
          (recCore_resp _ _ _) (ctorFieldsOf fd j) 0 ρp xs hclsA' hxs' hfnm
      have hmin' : fapps (ms.getD j pempty)
          (ihArgs fd.fref (recCore (mkM P μ) fd ms) (ctorFieldsOf fd j) xs) ∈
          Ed (mkM P μ) (fapps mo (idxv ++ [ctorV (mkM P μ) σ fd j xs])) :=
        mem_congr_left (fapps_congr_args _ hBridge) hmin
      exact mem_congr_right (ed_congr (mkM P μ)
        (fapps_congr_args mo (LEq_append (LEq.refl idxv)
          (show LEq [ctorV (mkM P μ) σ fd j xs] [dataVal j xs] from ⟨hzd, trivial⟩))))
        (mem_congr_left hrc.symm hmin')
    have hp : p ((DStar P μ fd σ ρp).Func i') :=
      motive_pred_resp P μ a vs ps mo ms (dataVal j xs) _ hFi.symm hpD
    exact mem_sep.mpr ⟨i', hp, hFi.trans (hdat.symm.trans hzi)⟩
  intro x hx idxv hl hfit hre
  obtain ⟨i, hpi, hxi⟩ := mem_sep.mp (DStar_least P μ fd hN σ ρp hType hsub x hx)
  exact (motive_pred_resp P μ a vs ps mo ms _ x hxi hpi) idxv hl hfit hre

/-- At a Π-recursive field, a denotation member is a functional graph over the
denoted domain: `den` of `.pi` is `piVal`, and every fibre at `pre ++ [y]` is
`DStar`-covered by `ed_recOcc_KTA`, hence never contains `∅`. -/
theorem fnField_piSet_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
    (ps : List PSet.{4}) (hps : ps.length = (famDataOf a).params.length)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (pre : List PSet.{4}) {A : Expr Nat}
    (hA : FnRec (famDataOf a).fref a.family.member.arity (famDataOf a).params.length
      (famDataOf a).indices.length pre.length A)
    (x : PSet.{4})
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) A)) :
    x ∈ piSet (Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) (piDom A)))
      (fun y => Ed (mkM P μ) (den (mkM P μ) (σOf vs)
        (vcons y (push pre (push ps ρ0))) (piCod A))) := by
  obtain ⟨D', idx, hAe, hlen, hD'f, hidxf⟩ := hA
  rw [hAe] at hx ⊢
  show x ∈ piSet (Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) D'))
    (fun y => Ed (mkM P μ) (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0)))
      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
        (policyParameterLocals (famDataOf a).params.length (pre.length + 1) ++ idx))))
  have hfib : ∀ y y', Equiv y y' →
      Equiv (den (mkM P μ) (σOf vs)
        (vcons y (push pre (push ps ρ0)))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length (pre.length + 1) ++ idx)))
        (den (mkM P μ) (σOf vs)
          (vcons y' (push pre (push ps ρ0)))
          (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
            (policyParameterLocals (famDataOf a).params.length (pre.length + 1) ++ idx))) :=
    fun y y' hy => den_congr _ _ _ (vcons_congr hy (fun i => Equiv.refl ((push pre (push ps ρ0)) i)))
  have hnone : ∀ y, y ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs)
      (push pre (push ps ρ0)) D') →
      ¬ pempty ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs)
        (vcons y (push pre (push ps ρ0)))
        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
          (policyParameterLocals (famDataOf a).params.length (pre.length + 1) ++ idx))) :=
    fun y _ hne => by
    have hvey : vcons y (push pre (push ps ρ0)) =
        push (pre ++ [y]) (push ps ρ0) := by
      rw [push_append]; rfl
    have hyl : (pre ++ [y]).length = pre.length + 1 := by
      rw [List.length_append, List.length_singleton]
    obtain ⟨hd', -⟩ := (ed_recOcc_KTA P μ a hKT G hN hf (σOf vs) hType ps
      (pre ++ [y]) hps idx hlen hidxf pempty).mp (by
        rw [← hvey, hyl]
        exact hne)
    exact (DStar_ne P μ (famDataOf a) hN (σOf vs) (push ps ρ0) pempty hd') Equiv.rfl
  exact mem_congr_right (ed_piVal_of_noEmpty (mkM P μ) hfib hnone) hx

/-- `fnFunctional_of_InPhi` at the `famKT` table: `TelFits` fields give the
`Ed`-membership, `fnField_piSet_KTA` the functional witness. -/
theorem fnFunctional_of_TelFits_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
    (ps : List PSet.{4}) (hpsl : ps.length = a.family.parameters.length)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length rest done.length →
      TelFits (mkM P μ) (σOf vs) rest (push pre (push ps ρ0)) xs →
      FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest
        (push pre (push ps ρ0)) xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls hT
      cases xs with
      | nil => trivial
      | cons x xs' => cases hT
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls hT
      obtain ⟨hdisj, hcls'⟩ := hcls
      cases xs with
      | nil => cases hT
      | cons x xs' =>
          obtain ⟨hx, htail⟩ := hT
          rcases hdisj with h0 | hdir | hFn
          · show (kindOf (famDataOf a).fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun h => ?_, ?_⟩
            · rw [kindOf_free h0] at h; cases h
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
          · show (kindOf (famDataOf a).fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun h => ?_, ?_⟩
            · rw [kindOf_directRec hdir] at h; cases h
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
          · obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            show (kindOf (famDataOf a).fref A = .fn → ∃ F : PSet.{4} → PSet.{4},
                (∀ y y', Equiv y y' → Equiv (F y) (F y')) ∧
                x ∈ piSet (Ed (mkM P μ)
                  (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)) (piDom A))) F) ∧
              FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest'
                (vcons x (push pre (push ps ρ0))) xs'
            refine ⟨fun _ => ?_, ?_⟩
            · exact ⟨fun y => Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                  (vcons y (push pre (push ps ρ0))) (piCod A)),
                fun y y' hy => ed_congr _
                  (den_congr _ _ _ (vcons_congr hy (fun i => Equiv.refl ((push pre (push ps ρ0)) i)))),
                fnField_piSet_KTA P μ a G vs ps hpsl hN hf hKT hType pre
                  (hpre.symm ▸ ⟨D', idx, hA, hlen, hD'f, hidxf⟩) x hx⟩
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClassA (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest'
          (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          FieldsClassA (famDataOf a).fref a.family.member.arity
            (famDataOf a).params.length (famDataOf a).indices.length rest'
            done'.length →
          TelFits (mkM P μ) (σOf vs) rest' (push pre (push ps ρ0)) xs →
          FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest'
            (push pre (push ps ρ0)) xs)
        (htail : TelFits (mkM P μ) (σOf vs) rest'
          (vcons x (push pre (push ps ρ0))) xs') :
        FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref rest'
          (vcons x (push pre (push ps ρ0))) xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x])
          (push ps ρ0) := by rw [push_append]; rfl
      rw [hvey] at htail ⊢
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        (by rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton, hpre])
        (by rw [List.length_append]; exact hcls') htail

/-- `ihChildL_of_InPhiA` at the `famKT` table from `TelFits`. -/
theorem ihChildL_of_TelFits_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
    (ps : List PSet.{4}) (hpsl : ps.length = a.family.parameters.length)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (Fs : List (Expr Nat)) {z : PSet.{4}} :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      (∀ y, y ∈ xs → MemT y z) →
      FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length rest done.length →
      TelFits (mkM P μ) (σOf vs) rest (push pre (push ps ρ0)) xs →
      ihChildL (famDataOf a).fref z rest xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hzm hcls hT
      trivial
  | cons A rest' IH =>
      intro pre xs hFs hpre hzm hcls hT
      obtain ⟨hdisj, hcls'⟩ := hcls
      cases xs with
      | nil => trivial
      | cons x xs' =>
          have hzm' : ∀ y, y ∈ xs' → MemT y z :=
            fun y hy => hzm y (List.mem_cons_of_mem x hy)
          have hxm : MemT x z := hzm x (List.mem_cons_self x xs')
          obtain ⟨hx, htail⟩ := hT
          rcases hdisj with h0 | hdir | hFn
          · refine ⟨fun hocc => ?_, ?_⟩
            · rw [hocc] at h0; exact Bool.noConfusion h0
            · exact ih_step done A rest' pre x xs' hFs hpre hzm' hcls' IH htail
          · obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hAe]
              exact ihChild_foldApps z (fun _ _ h => Expr.noConfusion h) _ x
            · exact ih_step done A rest' pre x xs' hFs hpre hzm' hcls' IH htail
          · obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hA]
              exact ihChild_pi_of_mem_piSet hxm
                (fun y y' hy => ed_congr _
                  (den_congr _ _ _ (vcons_congr hy (fun i => Equiv.refl ((push pre (push ps ρ0)) i)))))
                (fnField_piSet_KTA P μ a G vs ps hpsl hN hf hKT hType pre
                  (hpre.symm ▸ ⟨D', idx, hA, hlen, hD'f, hidxf⟩) x hx)
                (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _)
            · exact ih_step done A rest' pre x xs' hFs hpre hzm' hcls' IH htail
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hzm' : ∀ y, y ∈ xs' → MemT y z)
        (hcls' : FieldsClassA (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest'
          (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          (∀ y, y ∈ xs → MemT y z) →
          FieldsClassA (famDataOf a).fref a.family.member.arity
            (famDataOf a).params.length (famDataOf a).indices.length rest'
            done'.length →
          TelFits (mkM P μ) (σOf vs) rest' (push pre (push ps ρ0)) xs →
          ihChildL (famDataOf a).fref z rest' xs)
        (htail : TelFits (mkM P μ) (σOf vs) rest'
          (vcons x (push pre (push ps ρ0))) xs') :
        ihChildL (famDataOf a).fref z rest' xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x])
          (push ps ρ0) := by rw [push_append]; rfl
      rw [hvey] at htail
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        (by rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton, hpre])
        hzm'
        (by rw [List.length_append]; exact hcls') htail

/-- `ihOkA_of_InPhi` at the `famKT` table: direct fields' `Ed`-membership reads
`ed_recOcc_KTA` (non-sentinel ⇒ `argsFit` ⇒ index fit ⇒ `DStar_motiveA`),
Π-recursive fields go through `fnField_piSet_KTA` + `fapp_mem_piSet`. -/
theorem ihOkA_walk_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length)
    (hN : ∀ σ ρp (j : Fin (famDataOf a).ctors.length),
      NonIRSem P μ σ ρp (famDataOf a).fref ((famDataOf a).ctors.get j).1)
    (hf : (famDataOf a).fref ≠ 1 ∧ (famDataOf a).fref ≠ 2)
    (hKT : ∀ vs, Equiv (μ a.family.ref vs) (famKT P μ (famDataOf a) vs))
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val
          (a.constructorViews i).fields.length) ρ0 (a.constructors[i.val]).mtype))
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0)
      (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hType : evalTotal (σOf vs) (famDataOf a).resLevel ≠ 0)
    (Fs : List (Expr Nat)) :
    ∀ (done : List (Expr Nat)) (rest : List (Expr Nat)) (pre xs : List PSet.{4}),
      Fs = done ++ rest → pre.length = done.length →
      FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length rest done.length →
      TelFits (mkM P μ) (σOf vs) rest (push pre (push ps ρ0)) xs →
      IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
        (recCore (mkM P μ) (famDataOf a) ms)
        (shapesOf (famDataOf a).fref rest) rest (push pre (push ps ρ0)) xs := by
  intro done rest
  induction rest generalizing done with
  | nil =>
      intro pre xs hFs hpre hcls hT
      cases xs with
      | nil => trivial
      | cons x xs' => cases hT
  | cons A rest' IH =>
      intro pre xs hFs hpre hcls hT
      obtain ⟨hdisj, hcls'⟩ := hcls
      cases xs with
      | nil => cases hT
      | cons x xs' =>
          obtain ⟨hx, htail⟩ := hT
          rw [show shapesOf (famDataOf a).fref (A :: rest') =
              shapeOfKind (kindOf (famDataOf a).fref A) ::
                shapesOf (famDataOf a).fref rest' from rfl]
          rcases hdisj with h0 | hdir | hFn
          · rw [kindOf_free h0]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
              (recCore (mkM P μ) (famDataOf a) ms)
              (.nonrecursive :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun ho => ?_, fun ho => ?_, ?_⟩
            · cases ho
            · cases ho
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
          · obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
            rw [kindOf_directRec ⟨idx, hAe, hlen, hfree⟩]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
              (recCore (mkM P μ) (famDataOf a) ms)
              (.recursive 0 :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun _ => ?_, fun ho => ?_, ?_⟩
            · have hm : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                  (push pre (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length pre.length ++ idx))) := by
                rw [hAe, ← hpre] at hx
                exact hx
              obtain ⟨hd', hre⟩ := (ed_recOcc_KTA P μ a hKT G hN hf (σOf vs) hType
                ps pre hpsl idx hlen hfree x).mp hm
              have haf : argsFitF P μ (famDataOf a) (σOf vs) (push pre (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length done.length ++ idx)) := by
                cases hdec : P.dec (argsFitF P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length done.length ++ idx))) with
                | isTrue h => exact h
                | isFalse hn =>
                    exfalso
                    have hs : recTupAt P μ (famDataOf a) (σOf vs)
                        (push pre (push ps ρ0))
                        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                          (policyParameterLocals (famDataOf a).params.length
                            done.length ++ idx)) = singleton pempty := by
                      unfold recTupAt; rw [cond_neg hn]
                    rw [hpre] at hre
                    exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs)
                      (push ps ρ0) x (hre.trans (by rw [← hs]; exact Equiv.rfl))
              have hre2 : recTupAt P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length done.length ++ idx)) =
                  ordPair pempty (tup ((familyIdx (famDataOf a).params.length
                    (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                      (policyParameterLocals (famDataOf a).params.length
                        done.length ++ idx))).map
                    (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))) := by
                unfold recTupAt; rw [cond_pos haf]
              rw [familyIdx_directRec] at hre2
              have hre' : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0) x)
                  (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                    (push pre (push ps ρ0)))))) := by
                rw [← hre2]
                rw [hpre] at hre
                exact hre
              have hTf : TelFits (mkM P μ) (σOf vs)
                  ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                  ((policyParameterLocals (famDataOf a).params.length done.length ++ idx).map
                    (den (mkM P μ) (σOf vs) (push pre (push ps ρ0)))) :=
                (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                  (push pre (push ps ρ0)) (famDataOf a).fref
                  (canonL a.family.member.arity) _).mp haf
              have hpsl' : ps.length = (famDataOf a).params.length := hpsl
              have e := den_recArgs (mkM P μ) (σOf vs) ps pre idx
              rw [hpre] at e
              rw [← hpsl'] at hTf
              rw [e] at hTf
              obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
              obtain ⟨rfl, rfl⟩ := List.append_inj heq
                (by rw [TelFits.length h1]; exact hpsl')
              rw [hAe, familyIdx_directRec]
              exact DStar_motiveA P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo
                hms hType x hd'
                (idx.map (den (mkM P μ) (σOf vs) (push pre (push ps ρ0))))
                (by rw [List.length_map]; exact hlen) h2 hre'
            · cases ho
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
          · obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            rw [kindOf_fnRec ⟨D', idx, hA, hlen, hD'f, hidxf⟩]
            show IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
              (recCore (mkM P μ) (famDataOf a) ms)
              (.recursive 1 :: shapesOf (famDataOf a).fref rest') (A :: rest')
              (push pre (push ps ρ0)) (x :: xs')
            refine ⟨fun ho => ?_, fun _ y hy => ?_, ?_⟩
            · cases ho
            · rw [hA] at hy ⊢
              have hfib : ∀ y y', Equiv y y' →
                  Equiv (Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                    (vcons y (push pre (push ps ρ0)))
                    (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                      (policyParameterLocals (famDataOf a).params.length
                        (done.length + 1) ++ idx))))
                    (Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                      (vcons y' (push pre (push ps ρ0)))
                      (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                        (policyParameterLocals (famDataOf a).params.length
                          (done.length + 1) ++ idx)))) :=
                fun y y' hy => ed_congr _
                  (den_congr _ _ _ (vcons_congr hy (fun i => Equiv.refl ((push pre (push ps ρ0)) i))))
              have hxp : x ∈ piSet (Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                  (push pre (push ps ρ0)) D'))
                  (fun y => Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                    (vcons y (push pre (push ps ρ0)))
                    (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                      (policyParameterLocals (famDataOf a).params.length
                        (done.length + 1) ++ idx)))) := by
                have h := fnField_piSet_KTA P μ a G vs ps hpsl hN hf hKT hType pre
                  (hpre.symm ▸ ⟨D', idx, hA, hlen, hD'f, hidxf⟩) x hx
                rw [hA] at h
                exact h
              have hfy : fapp x y ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                  (vcons y (push pre (push ps ρ0)))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (done.length + 1) ++ idx))) :=
                fapp_mem_piSet hfib hxp hy
              have hvey : vcons y (push pre (push ps ρ0)) =
                  push (pre ++ [y]) (push ps ρ0) := by
                rw [push_append]; rfl
              have hyl : (pre ++ [y]).length = done.length + 1 := by
                rw [List.length_append, List.length_singleton, hpre]
              have hm' : fapp x y ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs)
                  (push (pre ++ [y]) (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (pre ++ [y]).length ++ idx))) := by
                rw [← hvey, hyl]
                exact hfy
              obtain ⟨hd', hre⟩ := (ed_recOcc_KTA P μ a hKT G hN hf (σOf vs) hType
                ps (pre ++ [y]) hpsl idx hlen hidxf (fapp x y)).mp hm'
              rw [hyl] at hre
              have haf : argsFitF P μ (famDataOf a) (σOf vs)
                  (push (pre ++ [y]) (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (done.length + 1) ++ idx)) := by
                cases hdec : P.dec (argsFitF P μ (famDataOf a) (σOf vs)
                  (push (pre ++ [y]) (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (done.length + 1) ++ idx))) with
                | isTrue h => exact h
                | isFalse hn =>
                    exfalso
                    have hs : recTupAt P μ (famDataOf a) (σOf vs)
                        (push (pre ++ [y]) (push ps ρ0))
                        (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                          (policyParameterLocals (famDataOf a).params.length
                            (done.length + 1) ++ idx)) = singleton pempty := by
                      unfold recTupAt; rw [cond_neg hn]
                    exact resTupF_ne_sentinel P μ (famDataOf a) (σOf vs)
                      (push ps ρ0) (fapp x y)
                      (hre.trans (by rw [← hs]; exact Equiv.rfl))
              have hre2 : recTupAt P μ (famDataOf a) (σOf vs)
                  (push (pre ++ [y]) (push ps ρ0))
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (done.length + 1) ++ idx)) =
                  ordPair pempty (tup ((familyIdx (famDataOf a).params.length
                    (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                      (policyParameterLocals (famDataOf a).params.length
                        (done.length + 1) ++ idx))).map
                    (den (mkM P μ) (σOf vs) (push (pre ++ [y]) (push ps ρ0))))) := by
                unfold recTupAt; rw [cond_pos haf]
              rw [familyIdx_directRec] at hre2
              have hre'' : Equiv (resTupF P μ (famDataOf a) (σOf vs) (push ps ρ0)
                  (fapp x y)) (ordPair pempty (tup (idx.map (den (mkM P μ) (σOf vs)
                    (push (pre ++ [y]) (push ps ρ0)))))) := by
                rw [← hre2]
                exact hre
              have hTf : TelFits (mkM P μ) (σOf vs)
                  ((famDataOf a).params ++ (famDataOf a).indices) ρ0
                  ((policyParameterLocals (famDataOf a).params.length
                    (done.length + 1) ++ idx).map
                    (den (mkM P μ) (σOf vs) (push (pre ++ [y]) (push ps ρ0)))) :=
                (argsFitF_directRec P μ (famDataOf a) (σOf vs)
                  (push (pre ++ [y]) (push ps ρ0)) (famDataOf a).fref
                  (canonL a.family.member.arity) _).mp haf
              have hpsl' : ps.length = (famDataOf a).params.length := hpsl
              have e := den_recArgs (mkM P μ) (σOf vs) ps (pre ++ [y]) idx
              rw [hyl] at e
              rw [← hpsl'] at hTf
              rw [e] at hTf
              obtain ⟨_, _, heq, h1, h2⟩ := TelFits_split _ _ ρ0 _ hTf
              obtain ⟨rfl, rfl⟩ := List.append_inj heq
                (by rw [TelFits.length h1]; exact hpsl')
              show (recCore (mkM P μ) (famDataOf a) ms) (fapp x y) ∈ Ed (mkM P μ)
                (fapps mo ((familyIdx (famDataOf a).params.length
                  (foldApps (.const (famDataOf a).fref (canonL a.family.member.arity))
                    (policyParameterLocals (famDataOf a).params.length
                      (done.length + 1) ++ idx))).map
                  (den (mkM P μ) (σOf vs) (vcons y (push pre (push ps ρ0))))
                  ++ [fapp x y]))
              rw [familyIdx_directRec, hvey]
              exact DStar_motiveA P μ a G vs ps mo ms hpsl hN hf hKT hctorμ hmo
                hms hType (fapp x y) hd'
                (idx.map (den (mkM P μ) (σOf vs) (push (pre ++ [y]) (push ps ρ0))))
                (by rw [List.length_map]; exact hlen) h2 hre''
            · exact ih_step done A rest' pre x xs' hFs hpre hcls' IH htail
  where
    ih_step (done : List (Expr Nat)) (A : Expr Nat) (rest' : List (Expr Nat))
        (pre : List PSet.{4}) (x : PSet.{4}) (xs' : List PSet.{4})
        (hFs : Fs = done ++ A :: rest') (hpre : pre.length = done.length)
        (hcls' : FieldsClassA (famDataOf a).fref a.family.member.arity
          (famDataOf a).params.length (famDataOf a).indices.length rest'
          (done.length + 1))
        (IH : ∀ (done' : List (Expr Nat)) (pre xs : List PSet.{4}),
          Fs = done' ++ rest' → pre.length = done'.length →
          FieldsClassA (famDataOf a).fref a.family.member.arity
            (famDataOf a).params.length (famDataOf a).indices.length rest'
            done'.length →
          TelFits (mkM P μ) (σOf vs) rest' (push pre (push ps ρ0)) xs →
          IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
            (recCore (mkM P μ) (famDataOf a) ms)
            (shapesOf (famDataOf a).fref rest') rest'
            (push pre (push ps ρ0)) xs)
        (htail : TelFits (mkM P μ) (σOf vs) rest'
          (vcons x (push pre (push ps ρ0))) xs') :
        IHOkA (mkM P μ) (σOf vs) (famDataOf a).params.length mo
          (recCore (mkM P μ) (famDataOf a) ms)
          (shapesOf (famDataOf a).fref rest') rest'
          (vcons x (push pre (push ps ρ0))) xs' := by
      have hvey : vcons x (push pre (push ps ρ0)) = push (pre ++ [x])
          (push ps ρ0) := by rw [push_append]; rfl
      rw [hvey] at htail ⊢
      exact IH (done ++ [A]) (pre ++ [x]) xs'
        (by rw [hFs]; exact (List.append_assoc done [A] rest').symm)
        (by rw [List.length_append, List.length_append,
          List.length_singleton, List.length_singleton, hpre])
        (by rw [List.length_append]; exact hcls') htail

/-- `ihChild` at a `pi` field whose value is any denotation member: under
`PiProp` the member is `≈ ∅` (empty graph domain, vacuous); otherwise it is a
functional graph and `ihChild_pi_of_mem_piSet` applies. No table premises. -/
theorem ihChild_of_mem_pi {M : Interp.{4}} {σ : Nat → Nat} {ρ : Nat → PSet.{4}}
    {z x : PSet.{4}} (hxz : MemT x z) {D B : Expr Nat}
    (hB : ∀ D' B', B ≠ .pi D' B')
    (hx : x ∈ Ed M (den M σ ρ (.pi D B))) : ihChild z (.pi D B) x := by
  have hd : den M σ ρ (.pi D B) =
      piVal M (den M σ ρ D) (fun y => den M σ (vcons y ρ) B) := rfl
  rw [hd] at hx
  unfold piVal at hx
  cases M.dec (PiProp M (den M σ ρ D) (fun y => den M σ (vcons y ρ) B)) with
  | isTrue hp =>
      rw [cond_pos hp] at hx
      have hx : x ∈ tv (∀ y, y ∈ Ed M (den M σ ρ D) →
          pempty ∈ Ed M (den M σ (vcons y ρ) B)) :=
        mem_congr_right (ed_tyv_of_dich M (dich_tv _)) hx
      obtain ⟨_, hxe⟩ := mem_tv.mp hx
      intro y hy
      exact (not_mem_pempty (mem_congr_right
        ((sImage_congr (fun a a' ha => pfst_congr ha) hxe).trans
          sImage_pfst_pempty) hy)).elim
  | isFalse hp =>
      rw [cond_neg hp] at hx
      have hx : x ∈ piSet (Ed M (den M σ ρ D))
          (fun y => Ed M (den M σ (vcons y ρ) B)) :=
        mem_congr_right (ed_tyv_of_dich M (dich_piSet M.dec
          (fun y y' hy => ed_congr M (den_congr M σ _ (vcons_congr hy
            (fun i => Equiv.refl (ρ i))))))) hx
      exact ihChild_pi_of_mem_piSet hxz
        (fun y y' hy => ed_congr _
          (den_congr _ _ _ (vcons_congr hy (fun i => Equiv.refl (ρ i)))))
        hx hB

/-- `ihChildL` from `TelFits` alone (no table): the `.fn` field's `ihChild` is
`ihChild_of_mem_pi`. -/
theorem ihChildL_of_TelFits (M : Interp.{4}) (σ : Nat → Nat) (f ar np nq : Nat)
    {z : PSet.{4}} :
    ∀ (d : Nat) (rest : List (Expr Nat)) (xs : List PSet.{4}) (ρ : Nat → PSet.{4}),
      (∀ y, y ∈ xs → MemT y z) →
      FieldsClassA f ar np nq rest d →
      TelFits M σ rest ρ xs →
      ihChildL f z rest xs := by
  intro d rest
  induction rest generalizing d with
  | nil => intro xs ρ hzm hcls hT; trivial
  | cons A rest' IH =>
      intro xs ρ hzm hcls hT
      obtain ⟨hdisj, hcls'⟩ := hcls
      cases xs with
      | nil => trivial
      | cons x xs' =>
          obtain ⟨hx, htail⟩ := hT
          have hzm' : ∀ y, y ∈ xs' → MemT y z :=
            fun y hy => hzm y (List.mem_cons_of_mem x hy)
          have hxm : MemT x z := hzm x (List.mem_cons_self x xs')
          rcases hdisj with h0 | hdir | hFn
          · refine ⟨fun hocc => ?_, ?_⟩
            · rw [hocc] at h0; exact Bool.noConfusion h0
            · exact IH (d + 1) xs' (vcons x ρ) hzm' hcls' htail
          · obtain ⟨idx, hAe, hlen, hfree⟩ := hdir
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hAe]
              exact ihChild_foldApps z (fun _ _ h => Expr.noConfusion h) _ x
            · exact IH (d + 1) xs' (vcons x ρ) hzm' hcls' htail
          · obtain ⟨D', idx, hA, hlen, hD'f, hidxf⟩ := hFn
            refine ⟨fun hocc => ?_, ?_⟩
            · rw [hA] at hx ⊢
              exact ihChild_of_mem_pi hxm
                (foldApps_ne_pi _ (fun _ _ h => Expr.noConfusion h) _) hx
            · exact IH (d + 1) xs' (vcons x ρ) hzm' hcls' htail

/-- **The recursor of a Π-recursive `Type` group is an element of its type** —
`recVal_mem_rec_KT` for `RecGroupA` at the `famKT` table. -/
theorem recVal_mem_rec_KTA (P : Premises4) (μ : Nat → List Nat → PSet.{4})
    {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (G : RecGroupA a) (vs : List Nat)
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
  refine recVal_mem_gen rfl a vs (famμ_of_KTA P μ a hKT G hN hf vs)
    (fun h0 => absurd h0 hType) (fun h0 => absurd h0 hType)
    (fun ps' is' j' xs' hcf => ?_)
    (recCore (mkM P μ) (famDataOf a)) (fun _ _ _ => rfl) ?_
  · obtain ⟨c, hc, hxs, _⟩ := hcf
    have hjk : j' < a.constructors.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      rwa [famDataOf_ctors_length] at this
    have hfo : ctorFieldsOf (famDataOf a) j' = (a.constructorViews ⟨j', hjk⟩).fields :=
      ctorFieldsOf_famDataOf a ⟨j', hjk⟩
    have hcc : c = ((a.constructorViews ⟨j', hjk⟩).fields,
        (a.constructorViews ⟨j', hjk⟩).resultIndices) := by
      have := famDataOf_ctor a ⟨j', hjk⟩
      rw [hc] at this
      exact Option.some.inj this
    rw [hcc] at hxs
    rw [hfo]
    exact ihChildL_of_TelFits (mkM P μ) (σOf vs) (famDataOf a).fref
      a.family.member.arity (famDataOf a).params.length (famDataOf a).indices.length
      0 ((a.constructorViews ⟨j', hjk⟩).fields) xs' (push ps' ρ0)
      (fun y hy => memT_dataVal hy) (G.fields ⟨j', hjk⟩) hxs
  · intro ps' mo' ms' is' _ hpsl hisl hmo hms hisfit j xs hcf
    rcases id hcf with ⟨c, hc, hxs, _⟩
    have hjk : j < a.constructors.length := by
      have := (List.getElem?_eq_some_iff.mp hc).1
      rwa [famDataOf_ctors_length] at this
    have hfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews ⟨j, hjk⟩).fields :=
      ctorFieldsOf_famDataOf a ⟨j, hjk⟩
    have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields,
        (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
      have := famDataOf_ctor a ⟨j, hjk⟩
      rw [hc] at this
      exact Option.some.inj this
    rw [hcc] at hxs
    have hmin := minor_ok_recA a G vs (famμ_of_KTA P μ a hKT G hN hf vs) hctorμ
      ps' mo' ms' is' hpsl hisl hmo hms hisfit j xs hcf
      (recCore (mkM P μ) (famDataOf a) ms') (recCore_resp _ _ _)
      (by rw [hfo]
          exact ihOkA_walk_KTA P μ a G vs ps' mo' ms' hpsl hN hf hKT hctorμ hmo
            hms hType ((a.constructorViews ⟨j, hjk⟩).fields) []
            ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
            (G.fields ⟨j, hjk⟩) hxs)
    have hxs' : xs.length = (ctorFieldsOf (famDataOf a) j).length := by
      rw [hfo]; exact hxs.length
    have hfnm : FnFunctional (mkM P μ) (σOf vs) (famDataOf a).fref
        (ctorFieldsOf (famDataOf a) j) (push ps' ρ0) xs := by
      rw [hfo]
      exact fnFunctional_of_TelFits_KTA P μ a G vs ps' hpsl hN hf hKT hType
        ((a.constructorViews ⟨j, hjk⟩).fields) []
        ((a.constructorViews ⟨j, hjk⟩).fields) [] xs rfl rfl
        (G.fields ⟨j, hjk⟩) hxs
    have hclsA' : FieldsClassA (famDataOf a).fref a.family.member.arity
        (famDataOf a).params.length (famDataOf a).indices.length
        (ctorFieldsOf (famDataOf a) j) 0 := by
      rw [hfo]; exact G.fields ⟨j, hjk⟩
    exact mem_congr_left (fapps_congr_args _
      (shArgsA_LEq_ihArgs (mkM P μ) (σOf vs) (famDataOf a).fref
        a.family.member.arity (famDataOf a).params.length
        (famDataOf a).indices.length (recCore (mkM P μ) (famDataOf a) ms')
        (recCore_resp _ _ _) (ctorFieldsOf (famDataOf a) j) 0 (push ps' ρ0) xs
        hclsA' hxs' hfnm)) hmin

end PSet

end Rcic.F3
