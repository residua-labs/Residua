import rcic.RcicF3PropEvalTyped
import rcic.RcicF3EvalPlanNormal
import rcic.RcicF3PropEvalPlain

/-!
# Field comparison from literal result indices and bounded proof rows

The existing singleton-Prop evaluation comparison asks for equality of the
ordinary field tuples at an equal full parameter/index key. This module
produces that comparison. A field literally exposed as a bare result index
is recovered from the key. Only the remaining fields need bounded typed
derivations at levels that evaluate to Prop.

The normalized bridge uses the actual EvalPlanNormal.fields telescope,
the unchanged resultIndices, and fields_forward at the same field values.
It does not replace a dependent telescope with an arity, erase parameters
from the key, or impose a bound on recursive Pi depth. The existing mutual
Eval proof continues to compare the actual typed IHs recursively.

This component does not change BoundG or any checked-tier antecedent.
Supplying the remaining bounded rows over the normalized telescope, and
threading the weaker bound through the other consumers, are separate debts.
The concrete non-vacuity witness is an indexed telescope over Sort 0; it is
not an imported Acc environment or a complete recursor instance.

Native verification: ROOT's pinned-toolchain run passed; all eight printed
declarations use only propext and Quot.sound. This component has not been
added to an RCC descriptor.
closure_claim = 0; scope_closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3.PSet.PropEvalSafeIndex

open Rcic.Declarative PiIndex PropEval
universe u v

/-- Equal-length parameter segments can be removed from a full key's LEq.
No equality or canonical representative of either segment is selected. -/
theorem leq_after_prefix (ps ps' xs xs' : List PSet.{u})
    (hl : ps.length = ps'.length) (h : LEq (ps ++ xs) (ps' ++ xs')) :
    LEq xs xs' := by
  induction ps generalizing ps' with
  | nil =>
      cases ps' with
      | nil => exact h
      | cons p' ps' => exact Nat.noConfusion hl
  | cons p ps ih =>
      cases ps' with
      | nil => exact Nat.noConfusion hl
      | cons p' ps' =>
          exact ih ps' (Nat.succ.inj hl) h.2

/-- Literal membership locates the same result-index read in both lists. -/
theorem leq_map_member {α : Type v} (f g : α → PSet.{u}) :
    (es : List α) → (e : α) → e ∈ es →
      LEq (es.map f) (es.map g) → Equiv (f e) (g e)
  | [], _, h, _ => by cases h
  | a :: es, e, h, he => by
      rcases List.mem_cons.mp h with rfl | h
      · exact he.1
      · exact leq_map_member f g es e h he.2

/-- The tuple relation follows from comparisons at all actual positions. -/
theorem leq_of_getD : (xs xs' : List PSet.{u}) → xs.length = xs'.length →
    (∀ j, j < xs.length → Equiv (xs.getD j pempty) (xs'.getD j pempty)) →
    LEq xs xs'
  | [], [], _, _ => True.intro
  | [], _ :: _, h, _ => Nat.noConfusion h
  | _ :: _, [], h, _ => Nat.noConfusion h
  | x :: xs, x' :: xs', hl, he => by
      refine ⟨he 0 (Nat.zero_lt_succ _), leq_of_getD xs xs' ?_ ?_⟩
      · exact Nat.succ.inj hl
      · intro j hj
        exact he (j + 1) (Nat.succ_lt_succ hj)

/-- A bare result local reads the original ordinary field, in declaration
order. Parameters remain below the whole ordinary field telescope. -/
theorem bare_field_read (M : Interp.{u}) (σ : Nat → Nat)
    (Fs : List (Expr Nat)) (xs : List PSet.{u}) (ρ : Nat → PSet.{u})
    (hl : xs.length = Fs.length) (j : Fin Fs.length) :
    den M σ (push xs ρ) (.bvar (Fs.length - 1 - j.val)) =
      xs.getD j.val pempty := by
  change push xs ρ (Fs.length - 1 - j.val) = _
  have hj : j.val < xs.length := by rw [hl]; exact j.isLt
  have hread : Fs.length - 1 - j.val < xs.length := by omega
  rw [push_lt xs ρ _ hread]
  have hpos : xs.length - 1 - (Fs.length - 1 - j.val) = j.val := by omega
  simp only [hpos, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hj, Option.getD_some]

/-- Full-key equality produces a comparison of each syntactically revealed
field. The parameter segment is retained until the key equality is used. -/
theorem field_equiv_of_key (M : Interp.{u}) (σ : Nat → Nat)
    (Fs Is : List (Expr Nat)) (j : Fin Fs.length)
    (hbare : Expr.bvar (Fs.length - 1 - j.val) ∈ Is)
    (ps ps' xs xs' : List PSet.{u}) (ρ : Nat → PSet.{u})
    (hpl : ps.length = ps'.length)
    (hxl : xs.length = Fs.length) (hxl' : xs'.length = Fs.length)
    (hkey : key (ps ++ Is.map (den M σ (push xs (push ps ρ)))) =
      key (ps' ++ Is.map (den M σ (push xs' (push ps' ρ))))) :
    Equiv (xs.getD j.val pempty) (xs'.getD j.val pempty) := by
  have hindices := leq_after_prefix ps ps' _ _ hpl ((key_eq_iff _ _).mp hkey)
  have hread := leq_map_member (den M σ (push xs (push ps ρ)))
    (den M σ (push xs' (push ps' ρ))) Is
    (.bvar (Fs.length - 1 - j.val)) hbare hindices
  rw [bare_field_read M σ Fs xs (push ps ρ) hxl j,
    bare_field_read M σ Fs xs' (push ps' ρ) hxl' j] at hread
  exact hread

/-- Bounded Prop typings are required only at fields absent from the bare
result-index positions. All contexts are actual dependent prefixes. -/
def UnrevealedBounds (S : ResolvedEnv) (ar : Nat) (σ K : Nat → Nat)
    (Ps Fs Is : List (Expr Nat)) : Prop :=
  ∀ j : Fin Fs.length, Expr.bvar (Fs.length - 1 - j.val) ∉ Is →
    ∃ l : Level, evalTotal σ l = 0 ∧
      ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + j.val))
        Fs[j] (.sort l), LOKt σ 4 K d

/-- The former all-proof row package implies this strictly conditional one.
No reverse implication is asserted. -/
theorem UnrevealedBounds.of_all {S : ResolvedEnv} {ar : Nat} {σ K : Nat → Nat}
    {Ps Fs Is : List (Expr Nat)}
    (h : ∀ j : Fin Fs.length, ∃ l : Level, evalTotal σ l = 0 ∧
      ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + j.val))
        Fs[j] (.sort l), LOKt σ 4 K d) :
    UnrevealedBounds S ar σ K Ps Fs Is := fun j _ => h j

/-- One bounded typed row makes its fitting value proof-like, without
requiring any earlier or later ordinary field to be a proof field. -/
theorem field_equiv_pempty_of_typing (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K σ : Nat → Nat)
    {S : ResolvedEnv} {ar : Nat} (Ps Fs : List (Expr Nat))
    (hES : EnvSound (mkM P μ) σ K S ar) (j : Fin Fs.length)
    (hB : ∃ l : Level, evalTotal σ l = 0 ∧
      ∃ d : HasTyT S ar (policyPrefixContext (Ps ++ Fs) (Ps.length + j.val))
        Fs[j] (.sort l), LOKt σ 4 K d)
    (ps xs : List PSet.{4}) (hps : TelFits (mkM P μ) σ Ps ρ0 ps)
    (hx : TelFits (mkM P μ) σ Fs (push ps ρ0) xs) :
    Equiv (xs.getD j.val pempty) pempty := by
  obtain ⟨l, h0, d, hd⟩ := hB
  have hz := TelFits.append hps hx
  have hk : Ps.length + j.val ≤ (Ps ++ Fs).length := by
    simp only [List.length_append]
    have := j.isLt
    omega
  have hf := fits_prefixContext (mkM P μ) σ (Ps ++ Fs) ρ0 (ps ++ xs)
    hz (Ps.length + j.val) hk
  have hs := sound_ty (P.good _ rfl) hES d hd _ hf
  have hpl : ps.length = Ps.length := hps.length
  have henv : push ((ps ++ xs).take (Ps.length + j.val)) ρ0 =
      push (xs.take j.val) (push ps ρ0) := by
    rw [← hpl, List.take_append_eq_append_take,
      List.take_of_length_le (by omega), push_append, Nat.add_sub_cancel_left]
  rw [henv] at hs
  have hsort : den (mkM P μ) σ (push (xs.take j.val) (push ps ρ0)) (.sort l) =
      tyv (U W4 0) := by
    change tyv (U W4 (evalTotal σ l)) = _
    rw [h0]
  rw [hsort] at hs
  have hX := mem_congr_right (ed_tyv (mkM P μ) (U4_dich 0)) hs
  exact ed_of_mem_U0 (mkM P μ) hX
    (TelFits_get Fs (push ps ρ0) xs hx j.val j.isLt)

/-- The full-field comparator is produced from syntax, typed bounded rows,
and the full result key. No semantic field-comparison callback is assumed. -/
theorem fields_equiv_of_bounds (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K σ : Nat → Nat)
    {S : ResolvedEnv} {ar : Nat} (Ps Fs Is : List (Expr Nat))
    (hES : EnvSound (mkM P μ) σ K S ar)
    (hB : UnrevealedBounds S ar σ K Ps Fs Is)
    (ps ps' xs xs' : List PSet.{4})
    (hps : TelFits (mkM P μ) σ Ps ρ0 ps)
    (hps' : TelFits (mkM P μ) σ Ps ρ0 ps')
    (hx : TelFits (mkM P μ) σ Fs (push ps ρ0) xs)
    (hx' : TelFits (mkM P μ) σ Fs (push ps' ρ0) xs')
    (hkey : key (ps ++ Is.map (den (mkM P μ) σ (push xs (push ps ρ0)))) =
      key (ps' ++ Is.map (den (mkM P μ) σ (push xs' (push ps' ρ0))))) :
    LEq xs xs' := by
  apply leq_of_getD xs xs' (hx.length.trans hx'.length.symm)
  intro k hk
  let j : Fin Fs.length := ⟨k, by rw [← hx.length]; exact hk⟩
  cases P.dec (Expr.bvar (Fs.length - 1 - j.val) ∈ Is) with
  | isTrue hbare =>
      exact field_equiv_of_key (mkM P μ) σ Fs Is j hbare ps ps' xs xs' ρ0
        (hps.length.trans hps'.length.symm) hx.length hx'.length hkey
  | isFalse hbare =>
      exact (field_equiv_pempty_of_typing P μ K σ Ps Fs hES j
        (hB j hbare) ps xs hps hx).trans
        (field_equiv_pempty_of_typing P μ K σ Ps Fs hES j
          (hB j hbare) ps' xs' hps' hx').symm

/-- Actual admission safety supplies the row split. Its untyped HasTy data
is not silently promoted to HasTyT or to a numerical bound. -/
theorem bounds_of_policy {E : ResolvedEnv} {fam : PolicyFamilyView E}
    {cm : CheckedMember} (cv : PolicyConstructorView E fam cm)
    (σ K : Nat → Nat) (hsafe : cv.AllFieldsSafe)
    (hB : ∀ j : Fin cv.fields.length, UniformProp (cv.fieldLevel j) →
      ∃ d : HasTyT E fam.member.arity
        (policyPrefixContext (cv.parameters ++ cv.fields) (cv.parameters.length + j.val))
        cv.fields[j] (.sort (cv.fieldLevel j)), LOKt σ 4 K d) :
    UnrevealedBounds E fam.member.arity σ K cv.parameters cv.fields cv.resultIndices := by
  intro j hbare
  have hp : UniformProp (cv.fieldLevel j) := (hsafe j).resolve_right hbare
  obtain ⟨d, hd⟩ := hB j hp
  exact ⟨cv.fieldLevel j, hp σ, d, hd⟩

/-- The singleton/empty Prop selection supplies the literal safe-field rule
for every constructor that actually exists. -/
theorem selected_fields_safe (C : Context)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (j : Fin C.node.a.constructors.length) :
    (C.node.a.constructorViews j).AllFieldsSafe := by
  have hs : EliminationSelection C.node.a.family.resultLevel
      C.node.a.constructors.length
      (∀ k, (C.node.a.constructorViews k).AllFieldsSafe) .anySort := by
    rw [← hpolicy]
    exact C.node.a.selected
  rcases (EliminationSelection.anySort_iff _ _ _).mp hs with ht | ⟨_, hz | ⟨_, hf⟩⟩
  · exact (Nat.pos_iff_ne_zero.mp (ht C.σ) h0).elim
  · have hj := j.isLt
    have hfalse : False := by omega
    exact hfalse.elim
  · exact hf j

/-- Composition with the existing actual-IH mutual theorem. Only ordinary
field comparison changes; recursive evaluation and typed IH alignment stay
in Eval.functional_of_field_comparison. -/
theorem functional_of_bounds (C : Context) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (S : ResolvedEnv) (ar : Nat) (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K S ar)
    (hB : ∀ j : Fin C.node.a.constructors.length,
      UnrevealedBounds S ar C.σ K C.node.a.family.parameters
        (C.node.a.constructorViews j).fields (C.node.a.constructorViews j).resultIndices)
    {i : Index.{4}} {z z' : PSet.{4}} (h : Eval C i z) (h' : Eval C i z') :
    Equiv z z' := by
  refine Eval.functional_of_field_comparison C
    (selection_prop C.node.a C.σ h0 hpolicy).2 ?_ h h'
  intro j ps ps' xs xs' hps hps' _ _ hx hx' hkey
  rw [hM] at hps hps' hx hx' hkey
  exact fields_equiv_of_bounds P μ K C.σ C.node.a.family.parameters
    (C.node.a.constructorViews j).fields (C.node.a.constructorViews j).resultIndices
    hES (hB j) ps ps' xs xs' hps hps' hx hx' hkey

/-- Comparison from the actual normalized telescope. Forward normalization
is performed at the two fitting tuples; dependent result syntax is retained
literally. No separate bound on the original unrevealed fields is assumed. -/
theorem fields_equiv_of_normalized_bounds (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K σ : Nat → Nat)
    {S : ResolvedEnv} {ar : Nat} (p : EvalPlan.Plan)
    (j : Fin p.node.a.constructors.length)
    (hES : EnvSound (mkM P μ) σ K S ar)
    (hδ : DeltaNormalize.BodyEquations (mkM P μ) p.node.E0 σ)
    (hB : UnrevealedBounds S ar σ K p.node.a.family.parameters
      (EvalPlanNormal.fields p j) (p.node.a.constructorViews j).resultIndices)
    (ps ps' xs xs' : List PSet.{4})
    (hps : TelFits (mkM P μ) σ p.node.a.family.parameters ρ0 ps)
    (hps' : TelFits (mkM P μ) σ p.node.a.family.parameters ρ0 ps')
    (hx : TelFits (mkM P μ) σ (p.node.a.constructorViews j).fields (push ps ρ0) xs)
    (hx' : TelFits (mkM P μ) σ (p.node.a.constructorViews j).fields (push ps' ρ0) xs')
    (hkey : key (ps ++ (p.node.a.constructorViews j).resultIndices.map
        (den (mkM P μ) σ (push xs (push ps ρ0)))) =
      key (ps' ++ (p.node.a.constructorViews j).resultIndices.map
        (den (mkM P μ) σ (push xs' (push ps' ρ0))))) : LEq xs xs' := by
  have hn := (EvalPlanNormal.fields_forward (mkM P μ) p.node.E0 σ hδ
    (p.constructors j).fields (push ps ρ0) xs hx).1
  have hn' := (EvalPlanNormal.fields_forward (mkM P μ) p.node.E0 σ hδ
    (p.constructors j).fields (push ps' ρ0) xs' hx').1
  exact fields_equiv_of_bounds P μ K σ p.node.a.family.parameters
    (EvalPlanNormal.fields p j) (p.node.a.constructorViews j).resultIndices
    hES hB ps ps' xs xs' hps hps' hn hn' hkey

/-- The normalized syntax and conditional proof rows produce functionality
of the original indexed evaluation, with the full parameter/index key. -/
theorem functional_of_normalized_bounds (C : Context) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (S : ResolvedEnv) (ar : Nat) (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K S ar)
    (hδ : DeltaNormalize.BodyEquations (mkM P μ) C.node.E0 C.σ)
    (hB : ∀ j : Fin C.node.a.constructors.length,
      UnrevealedBounds S ar C.σ K C.node.a.family.parameters
        (EvalPlanNormal.fields (EvalPlan.ofNode C.node) j)
        (C.node.a.constructorViews j).resultIndices)
    {i : Index.{4}} {z z' : PSet.{4}} (h : Eval C i z) (h' : Eval C i z') :
    Equiv z z' := by
  refine Eval.functional_of_field_comparison C
    (selection_prop C.node.a C.σ h0 hpolicy).2 ?_ h h'
  intro j ps ps' xs xs' hps hps' _ _ hx hx' hkey
  rw [hM] at hps hps' hx hx' hkey
  exact fields_equiv_of_normalized_bounds P μ K C.σ (EvalPlan.ofNode C.node) j
    hES hδ (hB j) ps ps' xs xs' hps hps' hx hx' hkey

/-- The plain-spine endpoint can be compared with an actual fitting
constructor tuple at the same full key. Revealed data fields are passed
to the stored minor unchanged; only unrevealed proof rows are compared
through proof irrelevance. This replaces the all-fields-erased equation
when proving iota for a safe-index constructor. -/
theorem plain_result_at_fields_of_bounds (C : Context) (P : Premises4)
    (μ : Nat → List Nat → PSet.{4}) (K : Nat → Nat)
    (S : ResolvedEnv) (ar : Nat) (hM : C.M = mkM P μ)
    (h0 : evalTotal C.σ C.node.a.family.resultLevel = 0)
    (hpolicy : C.node.a.policy = .anySort)
    (hES : EnvSound (mkM P μ) C.σ K S ar)
    (hB : ∀ j : Fin C.node.a.constructors.length,
      UnrevealedBounds S ar C.σ K C.node.a.family.parameters
        (C.node.a.constructorViews j).fields (C.node.a.constructorViews j).resultIndices)
    (hplain : ∀ (j : Fin C.node.a.constructors.length) s,
      s ∈ C.node.h14.shapesAt j → s = .nonrecursive)
    (j : Fin C.node.a.constructors.length) (ps xs : List PSet.{4})
    (hps : TelFits C.M C.σ C.node.a.family.parameters ρ0 ps)
    (hx : TelFits C.M C.σ (C.node.a.constructorViews j).fields (push ps ρ0) xs)
    {i : Index.{4}} {z : PSet.{4}} (h : Eval C i z)
    (hkey : i = key (ps ++ (C.node.a.constructorViews j).resultIndices.map
      (den C.M C.σ (push xs (push ps ρ0))))) :
    Equiv z (fapps (C.minors.getD j.val pempty) xs) := by
  cases h with
  | root j' ps' xs' ys fuel R out z hps' hp' hx' hs hst hd hm hi hr =>
      have hone := (selection_prop C.node.a C.σ h0 hpolicy).2
      have hj : j' = j := Fin.ext (by have := j'.isLt; have := j.isLt; omega)
      subst j'
      have he : LEq xs' xs := by
        rw [hM] at hps' hps hx' hx hkey
        exact fields_equiv_of_bounds P μ K C.σ C.node.a.family.parameters
          (C.node.a.constructorViews j).fields (C.node.a.constructorViews j).resultIndices
          hES (hB j) ps' ps xs' xs hps' hps hx' hx hkey
      rw [hi.plain_values (hplain j)] at hr
      exact hr.trans (fapps_congr_args _ he)

/-! ## A concrete indexed telescope with a data-valued field -/

def witnessTable : Nat → List Nat → PSet.{4} := fun _ _ => pempty
def witnessFields : List (Expr Nat) := [.sort .zero]
def witnessIndices : List (Expr Nat) := [.bvar 0]
def falseCode : PSet.{4} := tyv pempty
def trueCode : PSet.{4} := tyv (tv True)

theorem witness_prefix_sound (P : Premises4) (K σ : Nat → Nat) (ar : Nat) :
    EnvSound (mkM P witnessTable) σ K emptyEnv ar :=
  envSound_of_allSound P (fun _ _ h => by nomatch h)
    (fun _ _ h => by nomatch h) σ ar

theorem witness_bounds (K σ : Nat → Nat) :
    UnrevealedBounds emptyEnv 0 σ K [] witnessFields witnessIndices := by
  intro j hnot
  have hj : j.val = 0 := by
    have h := j.isLt
    simp only [witnessFields, List.length_cons, List.length_nil] at h
    omega
  apply False.elim
  apply hnot
  change Expr.bvar (1 - 1 - j.val) ∈ [Expr.bvar 0]
  rw [hj]
  exact List.mem_singleton.mpr rfl

theorem false_fits (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [falseCode] :=
  ⟨tyv_pempty_mem_sort P witnessTable σ ρ0 .zero, True.intro⟩

theorem true_fits (P : Premises4) (σ : Nat → Nat) :
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [trueCode] := by
  have ht : trueCode ∈ U W4 0 :=
    mem_sImage_tyv.mpr ⟨tv True,
      mem_propSets.mpr (fun _ hz => (mem_tv.mp hz).2), Equiv.rfl⟩
  exact ⟨mem_congr_right (ed_tyv (mkM P witnessTable) (U4_dich 0)).symm ht,
    True.intro⟩

/-- The revealed field is not silently treated as a proof value. -/
theorem false_code_not_proof : ¬ Equiv falseCode pempty := tyv_ne_pempty pempty

theorem distinct_codes (P : Premises4) : ¬ Equiv falseCode trueCode := by
  intro he
  have ht : pempty ∈ Ed (mkM P witnessTable) trueCode :=
    mem_congr_right (ed_tyv (mkM P witnessTable) (dich_tv True)).symm
      (mem_tv.mpr ⟨True.intro, Equiv.rfl⟩)
  have hf : pempty ∈ Ed (mkM P witnessTable) falseCode :=
    mem_congr_right (ed_congr (mkM P witnessTable) he).symm ht
  exact not_mem_pempty (mem_congr_right
    (ed_tyv (mkM P witnessTable) (Or.inl fun _ hz => (not_mem_pempty hz).elim)) hf)

/-- The producer's exact premises hold on a telescope with two inequivalent
data values. It still compares any two fitting tuples at the same full key. -/
theorem witness_comparison (P : Premises4) (K σ : Nat → Nat)
    (xs xs' : List PSet.{4})
    (hx : TelFits (mkM P witnessTable) σ witnessFields ρ0 xs)
    (hx' : TelFits (mkM P witnessTable) σ witnessFields ρ0 xs')
    (hkey : key (witnessIndices.map (den (mkM P witnessTable) σ (push xs ρ0))) =
      key (witnessIndices.map (den (mkM P witnessTable) σ (push xs' ρ0)))) :
    LEq xs xs' :=
  fields_equiv_of_bounds P witnessTable K σ [] witnessFields witnessIndices
    (witness_prefix_sound P K σ 0) (witness_bounds K σ)
    [] [] xs xs' True.intro True.intro hx hx' hkey

def Witness (P : Premises4) : Prop :=
  (∀ K σ ar, EnvSound (mkM P witnessTable) σ K emptyEnv ar) ∧
  (∀ K σ, UnrevealedBounds emptyEnv 0 σ K [] witnessFields witnessIndices) ∧
  (∀ σ, TelFits (mkM P witnessTable) σ witnessFields ρ0 [falseCode] ∧
    TelFits (mkM P witnessTable) σ witnessFields ρ0 [trueCode]) ∧
  ¬ Equiv falseCode pempty ∧ ¬ Equiv falseCode trueCode ∧
  (∀ (K : Nat → Nat) σ xs xs', TelFits (mkM P witnessTable) σ witnessFields ρ0 xs →
    TelFits (mkM P witnessTable) σ witnessFields ρ0 xs' →
    key (witnessIndices.map (den (mkM P witnessTable) σ (push xs ρ0))) =
      key (witnessIndices.map (den (mkM P witnessTable) σ (push xs' ρ0))) → LEq xs xs')

theorem component_witness (P : Premises4) : Witness P :=
  ⟨witness_prefix_sound P, witness_bounds, fun σ => ⟨false_fits P σ, true_fits P σ⟩,
    false_code_not_proof, distinct_codes P, witness_comparison P⟩

theorem component_nonrefutable (P : Premises4) :
    ¬ (Witness P → (Premises4 → False)) :=
  fun h => h (component_witness P) P

end Rcic.F3.PSet.PropEvalSafeIndex

#print axioms Rcic.F3.PSet.PropEvalSafeIndex.field_equiv_of_key
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.fields_equiv_of_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.functional_of_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.fields_equiv_of_normalized_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.functional_of_normalized_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.plain_result_at_fields_of_bounds
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.component_witness
#print axioms Rcic.F3.PSet.PropEvalSafeIndex.component_nonrefutable
