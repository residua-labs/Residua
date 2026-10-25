import rcic.RcicF3RecMemRec

/-!
# F3 S5b-3e: the recursor of a recursive group is sound

- `piLam_tables`, `famLE_tables`, `famEnd_tables`, `famVal_tables`: the
  family's value respects pointwise-`≈` tables;
- `DirectRec` / `FieldsClass`: a field is family-free or directly recursive
  (the family at its canonical instance applied to the parameter locals and
  family-free indices);
- `ihOkF_walk`: the motive condition at the recursive fields from a
  property of the recursive fields' sets;
- `RecGroup`: the S5b conditions on a group (levels bounded, parameters,
  indices and result indices family-free, fields classified, the family
  opaque, shapes matching fields);
- `rec_stage`: by induction on the stage of the family's iterates, a value
  `g` gives at each element of a fibre lies in the motive there (a recursive
  field lies one stage lower), given the closing step at a constructor;
- `recVal_mem_rec`: **the recursor of a recursive `Type` group is an element
  of its type** (`g` the recursor's computation), given that the family's
  entry is the limit of its iterates;
- `recVal_mem_recP`: the same for a recursive `Prop` group eliminating into
  `Prop` (`g` the proof `∅`; the motive is a proposition).

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

/-! ### pointwise-`≈` tables -/

section Tables

variable (P : Premises4) {μ₁ μ₂ : Nat → List Nat → PSet.{4}} (h : ∀ r ls, Equiv (μ₁ r ls) (μ₂ r ls))
include h

theorem piLam_tables (σ : Nat → Nat) {g₁ g₂ : (Nat → PSet.{4}) → PSet.{4}} (hg : EnvResp g₁)
    (hgg : ∀ ρ, Equiv (g₁ ρ) (g₂ ρ)) : (e : Expr Nat) → (ρ : Nat → PSet.{4}) →
    Equiv (piLam (mkM P μ₁) σ g₁ ρ e) (piLam (mkM P μ₂) σ g₂ ρ e)
  | .pi A B, ρ => lamVal_congr (mkM P μ₂) (den_tables P h σ A (fun _ => Equiv.rfl)) fun _ x' hx =>
      (piLam_congr (mkM P μ₁) σ hg B (vcons_congr (ρ := ρ) (ρ' := ρ) hx (fun _ => Equiv.rfl))).trans
        (piLam_tables σ hg hgg B (vcons x' ρ))
  | .bvar _, ρ => hgg ρ
  | .sort _, ρ => hgg ρ
  | .const _ _, ρ => hgg ρ
  | .app _ _, ρ => hgg ρ
  | .lam _ _, ρ => hgg ρ
  | .letE _ _ _, ρ => hgg ρ
  | .lit _, ρ => hgg ρ

theorem famLE_tables (W : PSet.{4}) (σ : Nat → Nat) (cs : List (List (Expr Nat) × List (Expr Nat))) :
    FamLE (mkM P μ₁) (mkM P μ₂) W σ cs where
  fields := fun _ _ A _ _ _ hz => mem_congr_right (ed_congr (mkM P μ₂) (den_tables P h σ A (fun _ => Equiv.rfl))) hz
  small := fun _ _ A _ _ hW => mem_congr_left (ed_congr (mkM P μ₂) (den_tables P h σ A (fun _ => Equiv.rfl))) hW
  ri := fun _ _ e _ _ => den_tables P h σ e (fun _ => Equiv.rfl)

theorem famEnd_tables (σ : Nat → Nat) (fd : FamData) (ρ : Nat → PSet.{4}) :
    Equiv (famEnd (mkM P μ₁) W4 σ fd ρ) (famEnd (mkM P μ₂) W4 σ fd ρ) := by
  have h' : ∀ r ls, Equiv (μ₂ r ls) (μ₁ r ls) := fun r ls => (h r ls).symm
  unfold famEnd cond
  dsimp only [mkM]
  cases P.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => PropFib_mono (famLE_tables P h (W4 0) σ fd.ctors) hz,
        fun hz => PropFib_mono (famLE_tables P h' (W4 0) σ fd.ctors) hz⟩)
  | isFalse _ =>
      exact tyv_congr (ext fun _ => ⟨fun hz => TypeFib_mono (famLE_tables P h _ σ fd.ctors) hz,
        fun hz => TypeFib_mono (famLE_tables P h' _ σ fd.ctors) hz⟩)

theorem famVal_tables (σ : Nat → Nat) (fd : FamData) :
    Equiv (famVal (mkM P μ₁) W4 σ fd) (famVal (mkM P μ₂) W4 σ fd) :=
  piLam_tables P h σ (famEnd_resp _ W4 σ fd) (famEnd_tables P h σ fd) (famType fd) _

end Tables

/-! ### directly recursive fields -/

/-- A directly recursive field at depth `d`: the family at its canonical
instance applied to the parameter locals and `nq` family-free indices. -/
def DirectRec (f ar np nq d : Nat) (A : Expr Nat) : Prop :=
  ∃ idx : List (Expr Nat), A = foldApps (.const f (canonL ar)) (policyParameterLocals np d ++ idx) ∧
    idx.length = nq ∧ ∀ e, e ∈ idx → occursConst f e = false

/-- Every field from depth `d` on is family-free or directly recursive. -/
def FieldsClass (f ar np nq : Nat) : List (Expr Nat) → Nat → Prop
  | [], _ => True
  | A :: Fs, d => (occursConst f A = false ∨ DirectRec f ar np nq d A) ∧ FieldsClass f ar np nq Fs (d + 1)

theorem FieldsClass.mem {f ar np nq : Nat} : {Fs : List (Expr Nat)} → {d : Nat} → FieldsClass f ar np nq Fs d →
    ∀ A, A ∈ Fs → occursConst f A = false ∨ ∃ d', DirectRec f ar np nq d' A
  | A :: Fs, d, ⟨hA, hFs⟩, B, hB => by
      rcases List.mem_cons.mp hB with rfl | hB
      · rcases hA with h | h
        · exact Or.inl h
        · exact Or.inr ⟨d, h⟩
      · exact FieldsClass.mem hFs B hB

theorem familyIdx_directRec (np d : Nat) (f : Nat) (ls : List Level) (idx : List (Expr Nat)) :
    familyIdx np (foldApps (.const f ls) (policyParameterLocals np d ++ idx)) = idx := by
  rw [familyIdx_foldApps_const, List.drop_append_of_le_length (by rw [length_paramLocals]; exact Nat.le_refl _),
    List.drop_eq_nil_of_le (by rw [length_paramLocals]; exact Nat.le_refl _), List.nil_append]

/-- The motive condition at the recursive fields, from a property of the
recursive fields' sets at a table `Mt`. -/
theorem ihOkF_walk (M Mt : Interp.{4}) (σ : Nat → Nat) (f ar np nq : Nat) (mo : PSet.{4})
    (g : PSet.{4} → PSet.{4}) (ps : List PSet.{4})
    (hR : ∀ (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4}), idx.length = nq →
      (∀ e, e ∈ idx → occursConst f e = false) →
      x ∈ Ed Mt (den Mt σ (push ys (push ps ρ0))
        (foldApps (.const f (canonL ar)) (policyParameterLocals np ys.length ++ idx))) →
      g x ∈ Ed M (fapps mo (idx.map (den M σ (push ys (push ps ρ0))) ++ [x]))) :
    (Fs : List (Expr Nat)) → (ys xs : List PSet.{4}) → FieldsClass f ar np nq Fs ys.length →
    TelFits Mt σ Fs (push ys (push ps ρ0)) xs → IHOkF M σ np mo g f Fs (push ys (push ps ρ0)) xs
  | [], _, _, _, _ => trivial
  | _ :: _, _, [], _, _ => trivial
  | A :: Fs, ys, x :: xs, ⟨hc, hcs⟩, ⟨hx, hfs⟩ => by
      refine ⟨fun ho => ?_, ?_⟩
      · rcases hc with h0 | ⟨idx, rfl, hl, hidx⟩
        · rw [h0] at ho; cases ho
        · rw [familyIdx_directRec]
          exact hR ys idx x hl hidx hx
      · have h1 : vcons x (push ys (push ps ρ0)) = push (ys ++ [x]) (push ps ρ0) := by rw [push_append]; rfl
        have hl : ys.length + 1 = (ys ++ [x]).length := by simp
        rw [hl] at hcs
        rw [h1] at hfs ⊢
        exact ihOkF_walk M Mt σ f ar np nq mo g ps hR Fs (ys ++ [x]) xs hcs hfs

/-! ### the recursor of a recursive group -/

/-- The S5b conditions on a group, read at its recursor's admission. -/
structure RecGroup {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) :
    Prop where
  bounded : FamBounded (famDataOf a) a.family.member.arity
  famFree : ∀ e, e ∈ a.family.parameters ++ a.family.indices → occursConst a.family.ref e = false
  fields : ∀ i : Fin a.constructors.length, FieldsClass a.family.ref a.family.member.arity
    a.family.parameters.length a.family.indices.length (a.constructorViews i).fields 0
  riFree : ∀ (i : Fin a.constructors.length) (e : Expr Nat), e ∈ (a.constructorViews i).resultIndices →
    occursConst a.family.ref e = false
  opq : ∀ ls, transparentBody E a.family.ref ls = none
  shapes : ∀ i : Fin a.constructors.length, ∃ fuel shapes, ShapesMatch a.family.ref shapes
    (a.constructorViews i).fields ∧ derivedMinor a i fuel shapes = a.minorTypes[i.val]?

theorem paramLocals_free (f np d : Nat) : ∀ e, e ∈ policyParameterLocals np d → occursConst f e = false := by
  intro e he
  unfold policyParameterLocals at he
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
  rfl

theorem RecGroup.cls {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    (G : RecGroup a) : ∀ c, c ∈ (famDataOf a).ctors → ∀ A, A ∈ c.1 →
      occursConst (famDataOf a).fref A = false ∨ RecApp (famDataOf a) a.family.member.arity A := by
  intro c hc A hA
  have hc' : c ∈ ofFin a.constructors.length
      (fun i => ((a.constructorViews i).fields, (a.constructorViews i).resultIndices)) := hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
  rcases (G.fields i).mem A hA with h | ⟨d, idx, rfl, hl, hidx⟩
  · exact Or.inl h
  · refine Or.inr ⟨policyParameterLocals a.family.parameters.length d ++ idx, rfl, ?_, fun e he => ?_⟩
    · simp only [List.length_append, length_paramLocals, hl]; rfl
    · rcases List.mem_append.mp he with he | he
      · exact paramLocals_free _ _ _ e he
      · exact hidx e he

theorem RecGroup.ri {E : ResolvedEnv} {r : Nat} {m : CheckedMember} {a : RecursorEliminationAdmitted E r m}
    (G : RecGroup a) : ∀ c, c ∈ (famDataOf a).ctors → ∀ e, e ∈ c.2 → occursConst (famDataOf a).fref e = false := by
  intro c hc e he
  have hc' : c ∈ ofFin a.constructors.length
      (fun i => ((a.constructorViews i).fields, (a.constructorViews i).resultIndices)) := hc
  obtain ⟨i, rfl⟩ := mem_ofFin _ _ hc'
  exact G.riFree i e he

section RecVal

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m)
  (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (famDataOf a) vs))

include hLim in
theorem tabLim_equiv : ∀ r' ls, Equiv (tabLim P μ (famDataOf a) r' ls) (μ r' ls) := by
  intro r' ls
  by_cases hr : r' = a.family.ref
  · subst hr
    show Equiv (upd μ a.family.ref (famLim P μ (famDataOf a)) a.family.ref ls) _
    rw [upd_eq]
    exact (hLim ls).symm
  · show Equiv (upd μ a.family.ref (famLim P μ (famDataOf a)) r' ls) _
    rw [upd_ne μ _ _ hr]
    exact Equiv.rfl

include hLim in
/-- The family's entry is the family's value, at every recursor instance. -/
theorem famμ_of_lim (G : RecGroup a) (vs : List Nat) :
    Equiv (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (famVal (mkM P μ) W4 (σOf vs) (famDataOf a)) :=
  (hLim _).trans ((famLim_fix P μ (famDataOf a) a.family.member.arity G.bounded G.famFree G.cls G.ri _).symm.trans
    ((famVal_levels (mkM P (tabLim P μ (famDataOf a))) (σOf_policyFamilyLevels_agree a.family vs) W4 _
      G.bounded).trans (famVal_tables P (tabLim_equiv P μ a hLim) _ _)))

/-- The stage claim: at every element of the family's fibre at stage `n`, the
value `g` gives lies in the motive there. -/
def StageOK (g : PSet.{4} → PSet.{4}) (vs : List Nat) (ps : List PSet.{4}) (mo : PSet.{4}) (n : Nat) : Prop :=
  ∀ (is : List PSet.{4}) (z : PSet.{4}), is.length = a.family.indices.length →
    TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
    z ∈ El (famEnd (mkM P (tabIter P μ (famDataOf a) n)) W4 (σOf vs) (famDataOf a) (push (ps ++ is) ρ0)) →
    g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z]))

/-- From a fibre at stage `m` read at the arguments of a recursive field. -/
theorem stage_of_fib (g : PSet.{4} → PSet.{4}) (vs : List Nat) (ps : List PSet.{4}) (mo : PSet.{4})
    (hpsl : ps.length = a.family.parameters.length)
    (m : Nat) (IH : StageOK P μ a g vs ps mo m) (idxv : List PSet.{4}) (x : PSet.{4})
    (hfit : TelFits (mkM P μ) (σOf vs) (a.family.parameters ++ a.family.indices) ρ0 (ps ++ idxv))
    (hx : x ∈ El (famEnd (mkM P (tabIter P μ (famDataOf a) m)) W4 (σOf vs) (famDataOf a) (push (ps ++ idxv) ρ0))) :
    g x ∈ Ed (mkM P μ) (fapps mo (idxv ++ [x])) := by
  obtain ⟨xs', ys', he, h1, h2⟩ := TelFits_split _ _ ρ0 _ hfit
  have hxl : xs'.length = ps.length := by rw [h1.length, hpsl]
  obtain ⟨rfl, rfl⟩ := List.append_inj he.symm hxl
  exact IH ys' x h2.length h2 hx

end RecVal

/-- The recursive arguments' values: the parameters, then the indices. -/
theorem den_recArgs (M : Interp.{4}) (σ : Nat → Nat) (ps ys : List PSet.{4}) (idx : List (Expr Nat)) :
    (policyParameterLocals ps.length ys.length ++ idx).map (den M σ (push ys (push ps ρ0))) =
      ps ++ idx.map (den M σ (push ys (push ps ρ0))) := by
  rw [List.map_append]
  have e : push ys (push ps ρ0) = push (ps ++ ys) ρ0 := (push_append ps ys ρ0).symm
  rw [e, den_paramLocals]

theorem recArgs_free (f np d : Nat) {idx : List (Expr Nat)} (hidx : ∀ e, e ∈ idx → occursConst f e = false) :
    ∀ e, e ∈ policyParameterLocals np d ++ idx → occursConst f e = false := fun e he => by
  rcases List.mem_append.mp he with he | he
  · exact paramLocals_free f np d e he
  · exact hidx e he

/-- An element of a fibre is a constructor's value at fitting fields. -/
theorem mem_el_famEnd {M : Interp.{4}} {σ : Nat → Nat} {fd : FamData} {ps is : List PSet.{4}} {z : PSet.{4}}
    (hl : is.length = fd.indices.length) (hz : z ∈ El (famEnd M W4 σ fd (push (ps ++ is) ρ0))) :
    ∃ j xs, CtorFits M σ fd.ctors (push ps ρ0) is j xs ∧ Equiv z (ctorV M σ fd j xs) := by
  unfold famEnd cond at hz
  have e1 : shiftρ fd.indices.length (push (ps ++ is) ρ0) = push ps ρ0 := by rw [← hl, push_append, shiftρ_push]
  have e2 : lastVals fd.indices.length (push (ps ++ is) ρ0) = is := by rw [← hl, push_append, lastVals_push]
  cases hd : M.dec (evalTotal σ fd.resLevel = 0) with
  | isTrue h0 =>
      rw [hd] at hz
      have hz' := mem_congr_right el_tyv hz
      rw [e1, e2] at hz'
      obtain ⟨⟨j, xs, hcf⟩, hz0⟩ := mem_tv.mp hz'
      refine ⟨j, xs, hcf, ?_⟩
      unfold ctorV cond
      rw [hd]
      exact hz0
  | isFalse h0 =>
      rw [hd] at hz
      have hz' := mem_congr_right el_tyv hz
      rw [e1, e2] at hz'
      obtain ⟨j, xs, c, hc, hcf, hzd, _⟩ := mem_TypeFib.mp hz'
      refine ⟨j, xs, hcf, ?_⟩
      unfold ctorV cond
      rw [hd]
      exact hzd

section Stage

variable (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
  (a : RecursorEliminationAdmitted E r m) (G : RecGroup a)
  (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (famDataOf a) vs)) (vs : List Nat)
  (hctorμ : ∀ i : Fin a.constructors.length,
    Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length) ρ0
        (a.constructors[i.val]).mtype))
  (ps : List PSet.{4}) (mo : PSet.{4}) (ms : List PSet.{4})
  (hpsl : ps.length = a.family.parameters.length)
  (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
  (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
  (g : PSet.{4} → PSet.{4})
  (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
    is.length = a.family.indices.length → TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
    z ∈ El (famEnd (mkM P (tabIter P μ (famDataOf a) n)) W4 (σOf vs) (famDataOf a) (push (ps ++ is) ρ0)) →
    CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs →
    Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs) z →
    fapps (ms.getD j pempty) (ihArgs a.family.ref g (ctorFieldsOf (famDataOf a) j) xs) ∈
      Ed (mkM P μ) (fapps mo (is ++ [z])) →
    g z ∈ Ed (mkM P μ) (fapps mo (is ++ [z])))
include G hLim hctorμ hpsl hmo hms hclose

/-- One step: the stage claim at `n`, given the recursive fields' values at `n`. -/
theorem rec_step (n : Nat)
    (hRn : ∀ (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4}), idx.length = a.family.indices.length →
      (∀ e, e ∈ idx → occursConst a.family.ref e = false) →
      x ∈ Ed (mkM P (tabIter P μ (famDataOf a) n)) (den (mkM P (tabIter P μ (famDataOf a) n)) (σOf vs)
        (push ys (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
          (policyParameterLocals a.family.parameters.length ys.length ++ idx))) →
      g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x]))) :
    StageOK P μ a g vs ps mo n := by
  intro is z hl hisfit hz
  obtain ⟨j, xs, hcf, hzc⟩ := mem_el_famEnd (fd := famDataOf a) hl hz
  rcases id hcf with ⟨c, hc, hxs, _⟩
  have hjk' : j < (famDataOf a).ctors.length := (List.getElem?_eq_some_iff.mp hc).1
  have hjk : j < a.constructors.length := by rwa [famDataOf_ctors_length] at hjk'
  have hC := famChain_iter P μ (famDataOf a) a.family.member.arity G.bounded G.famFree G.cls G.ri (σOf vs)
  have hcfM : CtorFits (mkM P μ) (σOf vs) (famDataOf a).ctors (push ps ρ0) is j xs :=
    CtorFits_mono (famLE_tables P (tabLim_equiv P μ a hLim) (W4 0) (σOf vs) _) (CtorFits_mono (hC.toLim n) hcf)
  have hfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews ⟨j, hjk⟩).fields :=
    ctorFieldsOf_famDataOf a ⟨j, hjk⟩
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  have hih : IHOkF (mkM P μ) (σOf vs) a.family.parameters.length mo g
      a.family.ref (ctorFieldsOf (famDataOf a) j) (push ps ρ0) xs := by
    rw [hfo]
    exact ihOkF_walk (mkM P μ) (mkM P (tabIter P μ (famDataOf a) n)) (σOf vs) a.family.ref a.family.member.arity
      a.family.parameters.length a.family.indices.length mo _ ps hRn _ [] xs (G.fields ⟨j, hjk⟩) hxs
  have hmin := minor_ok_rec a vs G.opq G.shapes (famμ_of_lim P μ a hLim G vs) hctorμ ps mo ms is hpsl hl hmo hms
    hisfit j xs hcfM _ hih
  have hcv : Equiv (ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs) z := hzc.symm
  exact hclose n is z j xs hl hisfit hz hcfM hcv
    (mem_congr_right (ed_congr _ (fapps_congr_args mo (LEq_append (LEq.refl is)
      (show LEq [ctorV (mkM P μ) (σOf vs) (famDataOf a) j xs] [z] from ⟨hcv, trivial⟩)))) hmin)

/-- **The stage claim at every stage.** -/
theorem rec_stage : ∀ n, StageOK P μ a g vs ps mo n := by
  intro n
  induction n with
  | zero =>
      refine rec_step P μ a G hLim vs hctorμ ps mo ms hpsl hmo hms g hclose 0 fun ys idx x hl hidx hx => ?_
      exact absurd (mem_congr_right (ed_rec_zero P μ (famDataOf a) a.family.member.arity G.bounded G.famFree (σOf vs)
        _ _ (recArgs_free _ _ _ hidx) (by simp only [List.length_append, length_paramLocals, hl]; rfl)) hx)
        not_mem_pempty
  | succ k ih =>
      refine rec_step P μ a G hLim vs hctorμ ps mo ms hpsl hmo hms g hclose (k + 1) fun ys idx x hl hidx hx => ?_
      have hargs := recArgs_free a.family.ref a.family.parameters.length ys.length hidx
      refine @Decidable.byCases _ _ (P.dec (RecFits P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
      · have hx' := mem_congr_right (ed_rec_succ_fit P μ (famDataOf a) a.family.member.arity G.bounded G.famFree k
          (σOf vs) _ _ hargs hfit) hx
        have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
        rw [hpsl] at e
        unfold RecFits at hfit
        rw [e] at hfit hx'
        exact stage_of_fib P μ a g vs ps mo hpsl k ih _ x hfit hx'
      · exact absurd (mem_congr_right (ed_rec_succ_nofit P μ (famDataOf a) a.family.member.arity G.bounded G.famFree k
          (σOf vs) _ _ hargs (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hx) not_mem_pempty

/-- The recursive fields' values lie in the motive, at the final table. -/
theorem rec_fields_ok (ys : List PSet.{4}) (idx : List (Expr Nat)) (x : PSet.{4})
    (hl : idx.length = a.family.indices.length) (hidx : ∀ e, e ∈ idx → occursConst a.family.ref e = false)
    (hx : x ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))
      (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx)))) :
    g x ∈ Ed (mkM P μ) (fapps mo (idx.map (den (mkM P μ) (σOf vs) (push ys (push ps ρ0))) ++ [x])) := by
  have hargs := recArgs_free a.family.ref a.family.parameters.length ys.length hidx
  have hxL : x ∈ Ed (mkM P (tabLim P μ (famDataOf a))) (den (mkM P (tabLim P μ (famDataOf a))) (σOf vs)
      (push ys (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyParameterLocals a.family.parameters.length ys.length ++ idx))) :=
    mem_congr_right (ed_congr _ (den_tables P (fun r' ls => (tabLim_equiv P μ a hLim r' ls).symm) (σOf vs) _
      (fun _ => Equiv.rfl))) hx
  refine @Decidable.byCases _ _ (P.dec (RecFits P μ (famDataOf a) (σOf vs) (push ys (push ps ρ0))
    (policyParameterLocals a.family.parameters.length ys.length ++ idx))) (fun hfit => ?_) (fun hfit => ?_)
  · obtain ⟨n, hn⟩ := mem_iUnionN.mp (mem_congr_right (ed_rec_lim_fit P μ (famDataOf a) a.family.member.arity G.bounded
      G.famFree (σOf vs) _ _ hargs hfit) hxL)
    have e := den_recArgs (mkM P μ) (σOf vs) ps ys idx
    rw [hpsl] at e
    unfold RecFits at hfit
    rw [e] at hfit hn
    exact stage_of_fib P μ a g vs ps mo hpsl n
      (rec_stage P μ a G hLim vs hctorμ ps mo ms hpsl hmo hms g hclose n) _ x hfit hn
  · exact absurd (mem_congr_right (ed_rec_lim_nofit P μ (famDataOf a) a.family.member.arity G.bounded G.famFree
      (σOf vs) _ _ hargs (by simp only [List.length_append, length_paramLocals, hl]; rfl) hfit) hxL) not_mem_pempty

end Stage

/-- The minor obligation of `recVal_mem_gen` for a recursive group, given the
closing step at each stage. -/
theorem minor_ok_group (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) (G : RecGroup a)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (famDataOf a) vs)) (vs : List Nat)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (ps : List PSet.{4}) (mo : PSet.{4}) (ms is : List PSet.{4})
    (hpsl : ps.length = a.family.parameters.length) (hisl : is.length = a.family.indices.length)
    (hmo : mo ∈ Ed (mkM P μ) (den (mkM P μ) (σOf vs) (push ps ρ0) (policyMotiveType a.family a.policy)))
    (hms : TelFits (mkM P μ) (σOf vs) a.minorTypes (vcons mo (push ps ρ0)) ms)
    (hisfit : TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is)
    (g : PSet.{4} → PSet.{4})
    (hclose : ∀ (n : Nat) (is : List PSet.{4}) (z : PSet.{4}) (j : Nat) (xs : List PSet.{4}),
      is.length = a.family.indices.length → TelFits (mkM P μ) (σOf vs) a.family.indices (push ps ρ0) is →
      z ∈ El (famEnd (mkM P (tabIter P μ (famDataOf a) n)) W4 (σOf vs) (famDataOf a) (push (ps ++ is) ρ0)) →
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
  have hfo : ctorFieldsOf (famDataOf a) j = (a.constructorViews ⟨j, hjk⟩).fields :=
    ctorFieldsOf_famDataOf a ⟨j, hjk⟩
  have hcc : c = ((a.constructorViews ⟨j, hjk⟩).fields, (a.constructorViews ⟨j, hjk⟩).resultIndices) := by
    have := famDataOf_ctor a ⟨j, hjk⟩
    rw [hc] at this; exact Option.some.inj this
  rw [hcc] at hxs
  refine minor_ok_rec a vs G.opq G.shapes (famμ_of_lim P μ a hLim G vs) hctorμ ps mo ms is hpsl hisl hmo hms hisfit
    j xs hcf _ ?_
  rw [hfo]
  exact ihOkF_walk (mkM P μ) (mkM P μ) (σOf vs) a.family.ref a.family.member.arity a.family.parameters.length
    a.family.indices.length mo _ ps (fun ys idx x hl hidx hx =>
      rec_fields_ok P μ a G hLim vs hctorμ ps mo ms hpsl hmo hms g hclose ys idx x hl hidx hx)
    _ [] xs (G.fields ⟨j, hjk⟩) hxs

/-- **The recursor of a recursive `Type` group is an element of its type.** -/
theorem recVal_mem_rec (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (G : RecGroup a)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (famDataOf a) vs)) (vs : List Nat)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (hType : evalTotal (σOf vs) a.family.resultLevel ≠ 0) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  refine recVal_mem_gen rfl a vs (famμ_of_lim P μ a hLim G vs) (fun h0 => absurd h0 hType) (fun h0 => absurd h0 hType)
    (recCore (mkM P μ) (famDataOf a)) (fun _ _ _ => rfl) ?_
  intro ps mo ms is _ hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_group P μ a G hLim vs hctorμ ps mo ms is hpsl hisl hmo hms hisfit _ ?_ j xs hcf
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

/-- **The recursor of a recursive `Prop` group eliminating into `Prop` is an
element of its type.** Its value is `∅`, the proof: by induction on the stage,
the motive holds at every inhabited instance, a recursive field's instance
being inhabited one stage lower. -/
theorem recVal_mem_recP (P : Premises4) (μ : Nat → List Nat → PSet.{4}) {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) (G : RecGroup a)
    (hLim : ∀ vs, Equiv (μ a.family.ref vs) (famLim P μ (famDataOf a) vs)) (vs : List Nat)
    (hctorμ : ∀ i : Fin a.constructors.length,
      Equiv (μ (a.family.ref + 1 + i.val) ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
        (piLam (mkM P μ) (σOf vs) (ctorEnd (mkM P μ) (σOf vs) (famDataOf a) i.val (a.constructorViews i).fields.length)
          ρ0 (a.constructors[i.val]).mtype))
    (hProp : evalTotal (σOf vs) a.family.resultLevel = 0) (hpol : a.policy = .propOnly) :
    piLam (mkM P μ) (σOf vs) (recEnd (mkM P μ) (σOf vs) (famDataOf a)) ρ0 m.mtype ∈
      Ed (mkM P μ) (den (mkM P μ) (σOf vs) ρ0 m.mtype) := by
  refine recVal_mem_gen rfl a vs (famμ_of_lim P μ a hLim G vs)
    (fun _ hp => by rw [hpol] at hp; cases hp) (fun _ hp => by rw [hpol] at hp; cases hp)
    (fun _ _ => pempty) (fun h0 => absurd hProp h0) ?_
  intro ps mo ms is hps hpsl hisl hmo hms hisfit j xs hcf
  refine minor_ok_group P μ a G hLim vs hctorμ ps mo ms is hpsl hisl hmo hms hisfit _ ?_ j xs hcf
  intro n is' z j' xs' hl' hisfit' hz _ _ hm
  -- the instance is inhabited at the limit, so the motive there is a proposition
  have hargs : ∀ e, e ∈ policyLocals (ps.length + is'.length) → occursConst a.family.ref e = false := by
    intro e he
    unfold policyLocals at he
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp he
    rfl
  have hden : (policyLocals (ps.length + is'.length)).map (den (mkM P μ) (σOf vs) (push is' (push ps ρ0))) =
      ps ++ is' := by
    rw [show push is' (push ps ρ0) = push (ps ++ is') ρ0 from (push_append ps is' ρ0).symm,
      show ps.length + is'.length = (ps ++ is').length by simp only [List.length_append], den_policyLocals]
  have hfit : RecFits P μ (famDataOf a) (σOf vs) (push is' (push ps ρ0)) (policyLocals (ps.length + is'.length)) := by
    unfold RecFits
    rw [hden]
    exact TelFits.append hps hisfit'
  have hzL : z ∈ Ed (mkM P (tabLim P μ (famDataOf a))) (den (mkM P (tabLim P μ (famDataOf a))) (σOf vs)
      (push is' (push ps ρ0)) (foldApps (.const a.family.ref (canonL a.family.member.arity))
        (policyLocals (ps.length + is'.length)))) := by
    refine mem_congr_right (ed_rec_lim_fit P μ (famDataOf a) a.family.member.arity G.bounded G.famFree
      (σOf vs) _ _ hargs hfit).symm (mem_iUnionN.mpr ⟨n, ?_⟩)
    rw [hden]
    exact hz
  have hzm : z ∈ Ed (mkM P μ) (fapps (μ a.family.ref ((policyFamilyLevels a.family).map (evalTotal (σOf vs))))
      (ps ++ is')) := by
    have h1 := mem_congr_right (ed_congr _ (den_tables P (tabLim_equiv P μ a hLim) (σOf vs) _
      (fun _ => Equiv.rfl))) hzL
    have h2 := Fapp_den (mkM P μ) (σOf vs) a.family.ref (canonL a.family.member.arity) ps is' ρ0
    rw [h2] at h1
    exact h1
  have hy := motive_prop_elem rfl a vs ps mo is' z hpsl hl' hpol hmo hisfit' hzm _ hm
  exact mem_congr_left hy hm

end PSet

end Rcic.F3
