import rcic.RcicF3DMinor

/-!
# F3 D-7: the recursor of a group with δ-hidden fields

The family is installed at the limit of the iterates of its **normalized**
data (`normFamData`), for which the recursive-group model applies verbatim
(`famLim_fix`, `famChain_iter`, `ed_rec_*`). The recursor's membership is the
stage induction of `RcicF3RecValRec` run on the normalized fibres, with the
minor obligation read on the original minor types (`minor_ok_recD`); the two
meet at the final table, where the original and normalized constructor lists
agree (`CtorsAgree`, from the fields' typings).

- `RecGroupD`: the conditions on a group read at its recursor's admission;
- `famμ_of_limD`: the family's entry is the normalized data's value; with the
  agreement, the original data's value (`famμ_of_lim_fd`);
- `recVal_mem_recD`: the recursor of a recursive `Type` group is an element
  of its type; `recVal_mem_recPD`: the same for a `Prop` group eliminating into
  `Prop`.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-- The conditions on a group with δ-hidden fields, read at its recursor's
admission, against the normalized data. -/
structure RecGroupD {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m)
    (fuelAt : Fin a.constructors.length → Nat) (shapesAt : Fin a.constructors.length → List FieldShape) : Prop where
  bounded : FamBounded (normFamData a fuelAt) a.family.member.arity
  famFree : ∀ e, e ∈ a.family.parameters ++ a.family.indices → occursConst a.family.ref e = false
  cls : ∀ c, c ∈ (normFamData a fuelAt).ctors → ∀ A, A ∈ c.1 →
    occursConst a.family.ref A = false ∨ RecApp (normFamData a fuelAt) a.family.member.arity A
  fields : ∀ i : Fin a.constructors.length, FieldsClass a.family.ref a.family.member.arity
    a.family.parameters.length a.family.indices.length
    ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) 0
  riFree : ∀ (i : Fin a.constructors.length) (e : Expr Nat), e ∈ (a.constructorViews i).resultIndices →
    occursConst a.family.ref e = false
  hcl : EnvClosed E
  shapes : ∀ i, ∃ fuel, ShapesNorm E fuel a.family.ref (shapesAt i) (a.constructorViews i).fields
    ((a.constructorViews i).fields.map (normField E (fuelAt i) a.family.ref)) ∧
    derivedMinor a i fuel (shapesAt i) = a.minorTypes[i.val]?

section RecVal

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m) {fuelAt : Fin a.constructors.length → Nat}
  {shapesAt : Fin a.constructors.length → List FieldShape} (G : RecGroupD a fuelAt shapesAt)
  (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (normFamData a fuelAt) vs))

omit hLim in
include G in
theorem RecGroupD.ri : ∀ c, c ∈ (normFamData a fuelAt).ctors → ∀ e, e ∈ c.2 → occursConst a.family.ref e = false := by
  intro c hc e he
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc
  exact G.riFree i e he

include hLim in
theorem tabLim_equivD : ∀ r' ls, Equiv (tabLim P μ (normFamData a fuelAt) r' ls) (μ r' ls) := by
  intro r' ls
  by_cases hr : r' = a.family.ref
  · subst hr
    show Equiv (upd μ a.family.ref (famLim P μ (normFamData a fuelAt)) a.family.ref ls) _
    rw [upd_eq]
    exact (hLim ls).symm
  · show Equiv (upd μ a.family.ref (famLim P μ (normFamData a fuelAt)) r' ls) _
    rw [upd_ne μ _ _ hr]
    exact Equiv.rfl

include G hLim in
/-- The family's entry is the normalized data's value, at every recursor instance. -/
theorem famμ_of_limD (vs : List Nat) :
    Equiv (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (normFamData a fuelAt)) :=
  (hLim _).trans ((famLim_fix P μ (normFamData a fuelAt) a.family.member.arity G.bounded G.famFree G.cls
    (RecGroupD.ri a G) _).symm.trans
    ((famVal_levels (mkM P (tabLim P μ (normFamData a fuelAt))) (σOf_policyFamilyLevels_agree a.family vs) W4 _
      G.bounded).trans (famVal_tables P (tabLim_equivD P μ a hLim) _ _)))

/-- The transfer at an instance: the original and normalized constructor lists
agree at every fitting parameter environment. -/
def AgreeAtD (vs : List Nat) : Prop :=
  ∀ ps, TelFits (mkM P μ) (σOf vs) a.family.parameters ρ0 ps →
    CtorsAgree (mkM P μ) (σOf vs) (famDataOf a).ctors (normFamData a fuelAt).ctors (push ps ρ0)

omit G hLim in
/-- The transfer transports to every instance agreeing with `vs` below the
family's arity (a recursor's instance carries one more level under `anySort`),
for level-bounded data. -/
theorem agreeAt_levels (vs vs' : List Nat) (h : ∀ i, i < a.family.member.arity → σOf vs i = σOf vs' i)
    (hB : FamBounded (famDataOf a) a.family.member.arity)
    (hB' : FamBounded (normFamData a fuelAt) a.family.member.arity)
    (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs) : AgreeAtD P μ a (fuelAt := fuelAt) vs' := by
  intro ps hps
  have hps' : TelFits (mkM P μ) (σOf vs) a.family.parameters ρ0 ps :=
    (TelFits_levels (mkM P μ) h a.family.parameters hB.params ρ0 ps).mpr hps
  exact CtorsAgree_levels (mkM P μ) h _ _ (fun c hc => (hB.ctors c hc).1) (fun c hc => (hB'.ctors c hc).1) _
    (hag ps hps')

include G hLim in
/-- With the transfer, the family's entry is the original data's value. -/
theorem famμ_of_lim_fd (vs : List Nat) (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs) :
    Equiv (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf a)) :=
  (famμ_of_limD P μ a G hLim vs).trans (famVal_agree (mkM P μ) W4 (σOf vs) (famDataOf a)
    (normFamData a fuelAt).ctors hag).symm

/-- The stage claim on the normalized fibres: at every element of the family's
fibre at stage `n`, the value `g` gives lies in the motive there. -/
def StageOKD (g : PSet.{4} → PSet.{4}) (vs : List Nat) (ps : List PSet.{4}) (mo : PSet.{4}) (n : Nat) : Prop :=
  ∀ (is : List PSet.{4}) (z : PSet.{4}), is.length = a.family.indices.length →
    TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
    z ∈ El (famEnd (mkM P (tabIter P μ (normFamData a fuelAt) n)) W4 (σOf vs) (normFamData a fuelAt)
      (push (ps ++ is) ρ0)) →
    g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z]))

theorem stage_of_fibD (g : PSet.{4} → PSet.{4}) (vs : List Nat) (ps : List PSet.{4}) (mo : PSet.{4})
    (hpsl : ps.length = a.family.parameters.length)
    (m : Nat) (IH : StageOKD P μ a (fuelAt := fuelAt) g vs ps mo m) (idxv : List PSet.{4}) (x : PSet.{4})
    (hfit : TelFits (mkM P μ) (σOf vs) (a.family.parameters ++ a.family.indices) ρ0 (ps ++ idxv))
    (hx : x ∈ El (famEnd (mkM P (tabIter P μ (normFamData a fuelAt) m)) W4 (σOf vs) (normFamData a fuelAt)
      (push (ps ++ idxv) ρ0))) :
    g x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])) := by
  obtain ⟨xs', ys', he, h1, h2⟩ := TelFits_split _ _ ρ0 _ hfit
  have hxl : xs'.length = ps.length := by rw [h1.length, hpsl]
  obtain ⟨rfl, rfl⟩ := List.append_inj he.symm hxl
  exact IH ys' x h2.length h2 hx

end RecVal

section Stage

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m) {fuelAt : Fin a.constructors.length → Nat}
  {shapesAt : Fin a.constructors.length → List FieldShape} (G : RecGroupD a fuelAt shapesAt)
  (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (normFamData a fuelAt) vs)) (vs : List Nat)
  (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs)
  (hctorμ : ∀ i : Fin a.constructors.length,
    Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
        (a.constructors[i.val]).mtype))
  (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
  (hps : TelFits (mkM P μ) (σOf vs) a.family.parameters ρ0 ps)
  (hpsl : ps.length = a.family.parameters.length)
  (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
  (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
  (g : PSet.{4} → PSet.{4})
  (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
    is.length = a.family.indices.length → TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
    z ∈ El (famEnd (mkM P (tabIter P μ (normFamData a fuelAt) n)) W4 (σOf vs) (normFamData a fuelAt)
      (push (ps ++ is) ρ0)) →
    CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs →
    Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs) z →
    fapps (ms.getD j pempty) (ihArgs a.family.ref g (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [z])) →
    g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z])))
include G hLim hag hctorμ hps hpsl hmo hms hclose

/-- One step: the stage claim at `n`, given the recursive fields' values at `n`. -/
theorem rec_stepD (n : Nat)
    (hRn : ∀ (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4}), idx.length = a.family.indices.length →
      (∀ e, e ∈ idx → occursConst a.family.ref e = false) →
      x ∈ Ed (mkM P (tabIter P μ (normFamData a fuelAt) n)) (den (mkM P (tabIter P μ (normFamData a fuelAt) n)) (σOf vs)
        (push ys (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
          (policyParameterLocals a.family.parameters.length ys.length ++ idx))) →
      g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x]))) :
    StageOKD P μ a (fuelAt := fuelAt) g vs ps mo n := by
  intro is z hl hisfit hz
  obtain ⟨j, xs, hcf, hzc⟩ := mem_el_famEnd (fd := normFamData a fuelAt) hl hz
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (normFamData a fuelAt).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < a.constructors.length := by rwa [normFamData_ctors_length] at hjk'
  have hC := famChain_iter P μ (normFamData a fuelAt) a.family.member.arity G.bounded G.famFree G.cls (RecGroupD.ri a G) (σOf vs)
  have hcfM : CtorFits (mkM P μ) (σOf vs) (normFamData a fuelAt).ctors (push ps ρ0) is j xs :=
    CtorFits_mono (famLE_tables P (tabLim_equivD P μ a hLim) (W4 0) (σOf vs) _) (CtorFits_mono (hC.toLim n) hcf)
  have hcfM0 : CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs :=
    (ctorFits_iff_of_agree _ _ (hag ps hps) is j xs).mpr hcfM
  have hfo : ctorFieldsOf (normFamData a fuelAt) j =
      (a.constructorViews ⟨j, hjk⟩).fields.map (normField E (fuelAt ⟨j, hjk⟩) a.family.ref) :=
    ctorFieldsOf_of_get (normFamData_ctor a fuelAt ⟨j, hjk⟩)
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields.map (normField E (fuelAt ⟨j, hjk⟩) a.family.ref),
      (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := normFamData_ctor a fuelAt ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  have hih : IHOkF (mkM P μ) (σOf vs) a.family.parameters.length mo g
      a.family.ref (ctorFieldsOf (normFamData a fuelAt) j) (push ps ρ0) xs := by
    rw [hfo]
    exact ihOkF_walk (mkM P μ) (mkM P (tabIter P μ (normFamData a fuelAt) n)) (σOf vs) a.family.ref
      a.family.member.arity a.family.parameters.length a.family.indices.length mo _ ps hRn _ [] xs
      (G.fields ⟨j, hjk⟩) hxs
  have hmin := minor_ok_recD a vs G.hcl fuelAt shapesAt G.shapes (famμ_of_lim_fd P μ a G hLim vs hag)
    hctorμ ps mo ms is hpsl hl hmo hms hisfit j xs hcfM0 _ hih
  have hcv : Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs) z := hzc.symm
  exact hclose n is z j xs hl hisfit hz hcfM0 hcv
    (mem_congr_right (ed_congr _ (fapps_congr_args mo (LEq_append (LEq.refl is)
      (show LEq [ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs] [z] from ⟨hcv, trivial⟩)))) hmin)

/-- **The stage claim at every stage.** -/
theorem rec_stageD : ∀ n, StageOKD P μ a (fuelAt := fuelAt) g vs ps mo n := by
  intro n
  induction n with
  | zero =>
      refine rec_stepD P μ a G hLim vs hag hctorμ ps mo ms hps hpsl hmo hms g hclose 0 fun ys idx x hl hidx hx => ?_
      exact absurd (mem_congr_right (ed_rec_zero P μ (normFamData a fuelAt) a.family.member.arity G.bounded G.famFree
        (σOf vs) _ _ (recArgs_free _ _ _ hidx) (by simp only [List.length_append, length_paramLocals, hl]; rfl)) hx)
        not_mem_pempty
  | succ k ih =>
      refine rec_stepD P μ a G hLim vs hag hctorμ ps mo ms hps hpsl hmo hms g hclose (k + 1)
        fun ys idx x hl hidx hx => ?_
      have hargs := recArgs_free a.family.ref a.family.parameters.length ys.length hidx
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ (normFamData a fuelAt) (σOf vs) (push ys (push ps ρ0))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
      · have hx' := mem_congr_right (ed_rec_succ_fit P μ (normFamData a fuelAt) a.family.member.arity G.bounded
          G.famFree k (σOf vs) _ _ hargs hfit) hx
        have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
        rw [hpsl] at e
        unfold RecFits at hfit
        rw [e] at hfit hx'
        exact stage_of_fibD P μ a g vs ps mo hpsl k ih _ x hfit hx'
      · exact absurd (mem_congr_right (ed_rec_succ_nofit P μ (normFamData a fuelAt) a.family.member.arity G.bounded
          G.famFree k (σOf vs) _ _ hargs (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hx)
          not_mem_pempty

/-- The recursive fields' values lie in the motive, at the final table. -/
theorem rec_fields_okD (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4})
    (hl : idx.length = a.family.indices.length) (hidx : ∀ e, e ∈ idx → occursConst a.family.ref e = false)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx)))) :
    g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x])) := by
  have hargs := recArgs_free a.family.ref a.family.parameters.length ys.length hidx
  have hxL : x ∈ Ed (mkM P (tabLim P μ (normFamData a fuelAt))) (den (mkM P (tabLim P μ (normFamData a fuelAt))) (σOf vs)
      (push ys (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx))) :=
    mem_congr_right (ed_congr _ (den_tables P (fun r' ls => (tabLim_equivD P μ a hLim r' ls).symm) (σOf vs) _
      (fun _ => Equiv.rfl))) hx
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ (normFamData a fuelAt) (σOf vs) (push ys (push ps ρ0))
    (policyParameterLocals a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (ed_rec_lim_fit P μ (normFamData a fuelAt)
      a.family.member.arity G.bounded G.famFree (σOf vs) _ _ hargs hfit) hxL)
    have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
    rw [hpsl] at e
    unfold RecFits at hfit
    rw [e] at hfit hn
    exact stage_of_fibD P μ a g vs ps mo hpsl n
      (rec_stageD P μ a G hLim vs hag hctorμ ps mo ms hps hpsl hmo hms g hclose n) _ x hfit hn
  · exact absurd (mem_congr_right (ed_rec_lim_nofit P μ (normFamData a fuelAt) a.family.member.arity G.bounded
      G.famFree (σOf vs) _ _ hargs (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hxL)
      not_mem_pempty

end Stage

/-- The minor obligation of `recVal_mem_gen` for a group with δ-hidden fields,
given the closing step at each stage. -/
theorem minor_ok_groupD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) {fuelAt : Fin a.constructors.length → Nat}
    {shapesAt : Fin a.constructors.length → List FieldShape} (G : RecGroupD a fuelAt shapesAt)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (normFamData a fuelAt) vs)) (vs : List Nat)
    (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (hps : TelFits (mkM P μ) (σOf vs) a.family.parameters ρ0 ps)
    (hpsl : ps.length = a.family.parameters.length) (hisl : is.length = a.family.indices.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hisfit : TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = a.family.indices.length → TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (normFamData a fuelAt) n)) W4 (σOf vs) (normFamData a fuelAt)
        (push (ps ++ is) ρ0)) →
      CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs →
      Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs) z →
      fapps (ms.getD j pempty) (ihArgs a.family.ref g (ctorFieldsOf (famDataOf a) j) xs) ∈
        Ed (mkM P μ) (fapps mo (is ++ [z])) →
      g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z])))
    (j : Nat) (xs : List PSet.{4}) (hcf : CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs) :
    fapps (ms.getD j pempty) (ihArgs (famDataOf a).fref g (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs])) := by
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (famDataOf a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < a.constructors.length := by rwa [famDataOf_ctors_length] at hjk'
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  -- the fitting fields fit the normalized telescope, at the final table
  obtain ⟨c', hc', hagj, _⟩ := (hag ps hps).get hc
  have hcc' : c' = ((a.constructorViews ⟨j, hjk⟩).fields.map (normField E (fuelAt ⟨j, hjk⟩) a.family.ref),
      (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := normFamData_ctor a fuelAt ⟨j, hjk⟩
    rw [hc'] at this; exact Option.some.inj this
  rw [hcc, hcc'] at hagj
  have hxs' := (telFits_iff_of_agree _ _ hagj xs).mp hxs
  have hfo' : ctorFieldsOf (normFamData a fuelAt) j =
      (a.constructorViews ⟨j, hjk⟩).fields.map (normField E (fuelAt ⟨j, hjk⟩) a.family.ref) :=
    ctorFieldsOf_of_get (normFamData_ctor a fuelAt ⟨j, hjk⟩)
  refine minor_ok_recD a vs G.hcl fuelAt shapesAt G.shapes (famμ_of_lim_fd P μ a G hLim vs hag) hctorμ ps mo
    ms is hpsl hisl hmo hms hisfit j xs hcf _ ?_
  rw [hfo']
  exact ihOkF_walk (mkM P μ) (mkM P μ) (σOf vs) a.family.ref a.family.member.arity a.family.parameters.length
    a.family.indices.length mo _ ps (fun ys idx x hl hidx hx =>
      rec_fields_okD P μ a G hLim vs hag hctorμ ps mo ms hps hpsl hmo hms g hclose ys idx x hl hidx hx)
    _ [] xs (G.fields ⟨j, hjk⟩) hxs'

/-- **The recursor of a recursive `Type` group with δ-hidden fields is an element
of its type.** -/
theorem recVal_mem_recD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) {fuelAt : Fin a.constructors.length → Nat}
    {shapesAt : Fin a.constructors.length → List FieldShape} (G : RecGroupD a fuelAt shapesAt)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (normFamData a fuelAt) vs)) (vs : List Nat)
    (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (hType : evalTotal (σOf vs) a.family.resultLevel ≠ 0) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  refine recVal_mem_gen rfl a vs (famμ_of_lim_fd P μ a G hLim vs hag) (fun h0 => absurd h0 hType)
    (fun h0 => absurd h0 hType) (recCore (mkM P μ) (famDataOf a)) (fun _ _ _ => rfl) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_groupD P μ a G hLim vs hag hctorμ ps mo ms is hps hpsl hisl hmo hms hisfit _ ?_ j xs hcf
  intro n is' z j' xs' _ _ _ hcf' hcv hm
  rcases id hcf' with ⟨c, hc, hxs, _⟩
  have hjk' : j' < (famDataOf a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hzd : Equiv z (dataVal j' xs') := by
    refine hcv.symm.trans ?_
    unfold ctorV cond
    dsimp only [mkM]
    cases P.dec (evalTotal (σOf vs) (famDataOf a).resLevel = 0) with
    | isTrue h => exact absurd h hType
    | isFalse _ => exact Equiv.rfl
  have hlen : xs'.length = nfOf (famDataOf a) j' := by unfold nfOf; rw [hc]; exact hxs.length
  exact mem_congr_left (recCore_data _ _ ms hzd hjk' hlen).symm hm

/-- **The recursor of a recursive `Prop` group with δ-hidden fields eliminating
into `Prop` is an element of its type.** -/
theorem recVal_mem_recPD (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) {fuelAt : Fin a.constructors.length → Nat}
    {shapesAt : Fin a.constructors.length → List FieldShape} (G : RecGroupD a fuelAt shapesAt)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (normFamData a fuelAt) vs)) (vs : List Nat)
    (hag : AgreeAtD P μ a (fuelAt := fuelAt) vs)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (hProp : evalTotal (σOf vs) a.family.resultLevel = 0) (hpol : a.policy = .propOnly) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  refine recVal_mem_gen rfl a vs (famμ_of_lim_fd P μ a G hLim vs hag)
    (fun _ hp => by rw [hpol] at hp; cases hp) (fun _ hp => by rw [hpol] at hp; cases hp)
    (fun _ _ => pempty) (fun h0 => absurd hProp h0) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_groupD P μ a G hLim vs hag hctorμ ps mo ms is hps hpsl hisl hmo hms hisfit _ ?_ j xs hcf
  intro n is' z j' xs' hl' hisfit' hz _ _ hm
  have hargs : ∀ e, e ∈ policyLocals (ps.length + is'.length) → occursConst a.family.ref e = false := by
    intro e he
    unfold policyLocals at he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    rfl
  have hden : (policyLocals (ps.length + is'.length)).map (den (mkM P μ) (σOf vs) (push is' (push ps ρ0))) =
      ps ++ is' := by
    rw [show push is' (push ps ρ0) = push (ps ++ is') ρ0 from (push_append ps is' ρ0).symm,
      show ps.length + is'.length = (ps ++ is').length by simp only [List.length_append], den_policyLocals]
  have hfit : RecFits P μ (normFamData a fuelAt) (σOf vs) (push is' (push ps ρ0))
      (policyLocals (ps.length + is'.length)) := by
    unfold RecFits
    rw [hden]
    exact TelFits.append hps hisfit'
  have hzL : z ∈ Ed (mkM P (tabLim P μ (normFamData a fuelAt))) (den (mkM P (tabLim P μ (normFamData a fuelAt))) (σOf vs)
      (push is' (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyLocals (ps.length + is'.length)))) := by
    refine mem_congr_right (ed_rec_lim_fit P μ (normFamData a fuelAt) a.family.member.arity G.bounded G.famFree
      (σOf vs) _ _ hargs hfit).symm (mem_iUnionN.mpr ⟨n, ?_⟩)
    rw [hden]
    exact hz
  have hzm : z ∈ Ed (mkM P μ) (fapps (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ is')) := by
    have h1 := mem_congr_right (ed_congr _ (den_tables P (tabLim_equivD P μ a hLim) (σOf vs) _
      (fun _ => Equiv.rfl))) hzL
    have h2 := Fapp_den (mkM P μ) (σOf vs) a.family.ref (canonL a.family.member.arity) ps is' ρ0
    rw [h2] at h1
    exact h1
  have hy := motive_prop_elem rfl a vs ps mo is' z hpsl hl' hpol hmo hisfit' hzm _ hm
  exact mem_congr_left hy hm

end PSet

end Rcic.F3
