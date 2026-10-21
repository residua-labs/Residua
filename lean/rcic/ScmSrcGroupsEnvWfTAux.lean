import rcic.ScmSrcGroupsFunRecTypedEq
import rcic.ScmSrcGroupsWf
import rcic.RcicTypedConv

/-! # K3c step 6 helpers — uniform `EnvWfT` obligation discharge over `srcEnvG`

`EnvWfT` (`RcicTypedEnv`) admits each `srcMembersG` member with a typed-judgment
derivation. The obligations are all of the form "the certified checker accepts
this term at this type", so each one is discharged by a `kernel_rfl_theorem`
leaf (an `.isSome = true` fact evaluated once, in the kernel) plus one of the
small combinators here, which lift the leaf to the judgment the constructor
asks for. No obligation is weakened: each leaf is the checker's own acceptance,
and `Option.get` exposes the derivation it carries.

* `sortTyAtC`: a term typed at a `Sort` after head steps; the pair
  `(sortTyAtC …).get h` is `⟨u, hT⟩` for `EnvWfT`'s `u`/`hT` fields.
* `finAllB`: `∀ i : Fin n` as a `List.range n |>.all` Bool (the same pattern
  `recIdxAdmittedTB` uses), so one kernel leaf covers a whole family.
* `famTypedB` / `ctorTypedB` / `ctorTypedAllB`: the `TelTypedT` domain typings
  inside a family/constructor view (and all views of a recursor admission),
  with `famTypedT_of` / `ctorTypedT_of` / `ctorTypedAll_of` lifting the
  `= true` leaf to `FamilyTypedT` / `CtorTypedT` / the per-index family.
* `admRecData`: the recursor admission's own `RecursorEliminationAdmitted`
  and `IotaDescriptorClause`, recovered from `IndGroupAdmitted` by matching —
  needed because the recursor leaves must be stated at the admission's ACTUAL
  descriptor (its `fuelAt`/`shapesAt` are data inside the matched record).
* `idxT_of`: `IdxAdmittedT` from the `recIdxAdmittedTB` leaf at the matched
  descriptor; at non-recursor members the obligation is `PUnit`.
* `iotaEqB`/`iotaEqsT_of`: per-constructor `IotaEquationTypedT` from
  `iotaEquationTypedT_of_check`, batched through `finAllB`.
* `wfTOfExtend`: `envPre_succ` transport, the `EnvWfT` analogue of
  `ScmSrcGroupsWf.wfOfExtend`.

Provenance: `ScmSrcGroupsEnvWfT0`–`ScmSrcGroupsEnvWfT17` are generated —
each region repeats the same shape (per-member `kernel_rfl_theorem`
leaf → `.get` → `wfTOfExtend` chain step) over the GROUPS/SINGLETONS
slot tables. The generator is `gen_wft.py` (git blob
`869d2ae54765337374bc91a75591ac1abe1ab346`, last present at `c45db2c3f3^`;
usage `gen_wft.py full <outdir>`), a dev-side script deliberately NOT
tracked in the tree: nf-admission refuses new `.py` files outright
(`[ci_nf_new_python]`, code 1 — the cut-8 repair channel covers growth
in EXISTING .py only). Correctness does not depend on the generator:
every emitted leaf is a `kernel_rfl_theorem` — the kernel re-checks the
checker's own acceptance — so the recipe being recoverable from any
region file plus the slot tables derivable from `srcMembersG` is a
convenience, not a trust premise.
-/

open Rcic.Declarative Rcic.Scm.SrcG
set_option maxRecDepth 8192
namespace Rcic.Scm.SrcG

/-- `∀ i : Fin n, f i` as one Bool: the `List.range`/`dif` pattern
    `recIdxAdmittedTB` uses. -/
def finAllB (n : Nat) (f : (i : Nat) → i < n → Bool) : Bool :=
  (List.range n).all fun j => if hj : j < n then f j hj else false

theorem finAllB_sound {n : Nat} {f : (i : Nat) → i < n → Bool}
    (h : finAllB n f = true) (i : Fin n) : f i.val i.isLt = true := by
  unfold finAllB at h
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  rw [dif_pos i.isLt] at hi
  exact hi

/-- `checkC`'s answer read as a sort after head steps: `⟨u, HasTyT e (.sort u)⟩`
    when the term is typed and its type converts to a sort within `fuel`. -/
def sortTyAtC (E : ResolvedEnv) (n fuel : Nat) (Γ : LCtx) (e : Expr Nat) :
    Option (Σ u, HasTyT E n Γ e (.sort u)) :=
  match checkC E n fuel Γ e with
  | some ⟨T, d⟩ => (toSort? E n fuel Γ T).map fun s => ⟨s.1, hasTyT_of_tyConv d s.2⟩
  | none => none

/-- the per-domain Bool of a `TelTypedT`: domain `i` in its prefix context is
    typed at `.sort (levels i)` by the conversion checker at `fuel`. -/
def telDomB (E : ResolvedEnv) (n fuel : Nat) (ds : List (Expr Nat))
    (levels : Fin ds.length → Level) (i : Nat) (hi : i < ds.length) : Bool :=
  (tyAtC E n fuel (policyPrefixContext ds i) (ds[i]'hi)
    (.sort (levels ⟨i, hi⟩))).isSome

/-- one `.all` leaf covers a whole telescope: `TelTypedT` from the per-domain
    conversion checks. -/
theorem telTypedT_of {E : ResolvedEnv} {n fuel : Nat} {ds : List (Expr Nat)}
    {levels : Fin ds.length → Level}
    (h : finAllB ds.length (telDomB E n fuel ds levels) = true) :
    TelTypedT E n ds levels := by
  intro i
  have hi := finAllB_sound h i
  exact ⟨(tyAtC _ _ _ _ _ _).get hi⟩

/-- a family view's typed content (`FamilyTypedT`), Bool form. -/
def famTypedB (E : ResolvedEnv) (fuel : Nat) (v : PolicyFamilyView E) : Bool :=
  finAllB (v.parameters ++ v.indices).length
    (telDomB E v.member.arity fuel (v.parameters ++ v.indices) v.domainsTyped.levels)

/-- `FamilyTypedT` from the `.all` leaf. -/
theorem famTypedT_of {E : ResolvedEnv} (v : PolicyFamilyView E) {fuel : Nat}
    (h : famTypedB E fuel v = true) : FamilyTypedT v := by
  unfold famTypedB at h
  exact telTypedT_of h

/-- a constructor view's typed content (`CtorTypedT`), Bool form: the
    `parameters ++ fields` telescope typed domain-wise, and each parameter a
    `TyConvT` of the family's parameter (05 §6's mirror). -/
def ctorTypedB {E : ResolvedEnv} {fam : PolicyFamilyView E} {m : CheckedMember}
    (fuel : Nat) (c : PolicyConstructorView E fam m) : Bool :=
  finAllB (c.parameters ++ c.fields).length
    (telDomB E fam.member.arity fuel (c.parameters ++ c.fields)
      c.domainsTyped.levels)
  && finAllB c.parameters.length fun i hi =>
    (tyConv? E fam.member.arity fuel (policyPrefixContext c.parameters i)
      c.parameters[i]
      (fam.parameters[i]'(by rw [← c.parameterCount]; exact hi))).isSome

/-- `CtorTypedT` from the `.all` leaf. -/
theorem ctorTypedT_of {E : ResolvedEnv} {fam : PolicyFamilyView E}
    {m : CheckedMember} {c : PolicyConstructorView E fam m} {fuel : Nat}
    (h : ctorTypedB fuel c = true) : CtorTypedT c := by
  unfold ctorTypedB at h
  rw [Bool.and_eq_true] at h
  exact ⟨fun i => ⟨(tyAtC _ _ _ _ _ _).get (finAllB_sound h.1 i)⟩,
    fun i => ⟨(tyConv? _ _ _ _ _ _).get (finAllB_sound h.2 i)⟩⟩

/-- `∀ i, CtorTypedT (a.constructorViews i)` at a recursor admission, Bool form. -/
def ctorTypedAllB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (fuel : Nat) (a : RecursorEliminationAdmitted E r m) : Bool :=
  finAllB a.constructors.length fun _ hi =>
    ctorTypedB fuel (a.constructorViews ⟨_, hi⟩)

theorem ctorTypedAll_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {fuel : Nat}
    (h : ctorTypedAllB fuel a = true) : ∀ i, CtorTypedT (a.constructorViews i) := by
  intro i
  have hi := finAllB_sound h i
  exact ctorTypedT_of hi

/-- the family admission's own view, recovered by matching. -/
def admFamView? {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) :
    Option (PolicyFamilyView (extendEnv E r m)) :=
  match hadm with
  | .family _ v _ _ _ => some v
  | _ => none

/-- the constructor admission's own family/constructor views, recovered by
    matching. -/
def admCtorViews? {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) :
    Option (Σ (f : PolicyFamilyView E) (mm : CheckedMember),
      PolicyConstructorView E f mm) :=
  match hadm with
  | .constructor f v _ _ _ _ _ => some ⟨f, _, v⟩
  | _ => none

/-- the recursor admission's own `a` and `h14`, recovered by matching: the
    descriptor's `fuelAt`/`shapesAt` are data inside `hadm`, and the
    `recIdxAdmittedTB`/`IotaEquationTypedT` leaves must be stated at that
    very descriptor (proof irrelevance then equates the Prop fields). -/
def admRecData {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (hadm : IndGroupAdmitted E r m) :
    Option (Σ (a : RecursorEliminationAdmitted E r m), IotaDescriptorClause E a) :=
  match hadm with
  | .recursor a _ _ _ _ _ h14 => some ⟨a, h14⟩
  | _ => none

/-- `IdxAdmittedT` from the decidable `recIdxAdmittedTB` check at the
    admission's own (matched) descriptor. At a non-recursor admission the
    obligation is `PUnit`; the `true` leaf there is `rfl`. -/
def idxT_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember} :
    (hadm : IndGroupAdmitted E r m) →
    (match hadm with
      | .recursor a _ _ _ _ _ h14 => recIdxAdmittedTB a h14
      | _ => true) = true →
    IdxAdmittedT hadm
  | .recursor a _ _ _ _ _ h14, h => .ofCheck a h14 h
  | .family .., _ => PUnit.unit
  | .constructor .., _ => PUnit.unit

/-- the per-constructor Bool of an `IotaEquationTypedT`: the schema reduct is
    typed by `check` at the equation type in the equation's context, in the
    derivation scope `extendEnv E r m`. -/
def iotaEqB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {h14 : IotaDescriptorClause E a}
    (check : (Γ : LCtx) → (e T : Expr Nat) →
      Option (HasTyT (extendEnv E r m) m.arity Γ e T))
    (i : Nat) (hi : i < a.constructors.length) : Bool :=
  match equationDoms a ⟨i, hi⟩, iotaSchemaAt a ⟨i, hi⟩ (h14.fuelAt ⟨i, hi⟩)
      (h14.shapesAt ⟨i, hi⟩) with
  | some doms, some rhs =>
      (check (assumptionCtx doms) rhs (iotaEquationType a ⟨i, hi⟩)).isSome
  | _, _ => false

/-- `∀ i, IotaEquationTypedT a i (h14.fuelAt i) (h14.shapesAt i)` from one
    `.all` leaf. -/
theorem iotaEqsT_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {h14 : IotaDescriptorClause E a}
    {check : (Γ : LCtx) → (e T : Expr Nat) →
      Option (HasTyT (extendEnv E r m) m.arity Γ e T)}
    (h : finAllB a.constructors.length (iotaEqB (h14 := h14) check) = true) :
    ∀ i, IotaEquationTypedT a i (h14.fuelAt i) (h14.shapesAt i) := by
  intro i
  have hi := finAllB_sound h i
  exact iotaEquationTypedT_of_check check hi

/-- `EnvWfT (extendEnv (envPre r) r m)` transported to `EnvWfT (envPre (r+1))`
    — the `ScmSrcGroupsWf.wfOfExtend` step on the typed judgment. -/
def wfTOfExtend {r : Nat} {m : CheckedMember}
    (hr : r < srcMembersG.length) (hm : srcMembersG[r]'hr = ⟨r, m⟩)
    (h : EnvWfT (extendEnv (envPre r) r m)) : EnvWfT (envPre (r+1)) := by
  rw [envPre_succ hr, hm]
  exact h

/-! ### Decomposed `recIdxAdmittedTB` (the K3c ValueAt split, generic form)

`recIdxAdmittedTB`'s whole-evaluation exceeds the deterministic kernel budget
on the indexed groups — both in one pass and cumulatively per file — so the
check is decomposed exactly as `ScmSrcGroupsFunRecTypedVA` did for
`aRecValueAt`: `recCtorCheckB` is the now-public `Rcic.Declarative`
`recIdxCtorB` conjunct under its local alias; `recTelCm` rewrites the
lifted-telescope
`constsMemberFuel` into the field sweep plus the small family-application
check (via `Rcic.Declarative`'s `constsMemberFuel_lift`/`policyPi_eq_foldr`
and `FunRecTyped`'s `constsMemberFuel_foldr_pi`); `recResCm` discharges the family-application
check; `recCtorCheckB_of` reassembles one constructor's conjunct from leaves;
`recIdxAdmittedB_of` reassembles the whole Bool from a per-constructor
`recCtorCheckB` family plus the three member-level leaves. -/

/-- `(extendEnv E r m).members r'` at an unrelated key is `E.members r'` —
    single-owned by `FunRecTyped.extendEnv_members_ne` (sealed there); kept as
    an alias so the generated region files name it unqualified. -/
theorem extendEnv_members_ne {E : ResolvedEnv} {r r' : Nat} {m : CheckedMember}
    (hne : r' ≠ r) :
    (extendEnv E r m).members r' = E.members r' :=
  FunRecTyped.extendEnv_members_ne hne

/-- `recIdxCtorB` under the name the generated region files use, so each
    conjunct can be a `kernel_rfl_theorem` leaf.  Single-owned by the public
    `Rcic.Declarative.recIdxCtorB` (#6197's dedupe made it public for exactly
    this); an `abbrev` keeps definitional unfolding transparent for the
    `.get`/leaf consumers. -/
abbrev recCtorCheckB {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) : Bool :=
  Rcic.Declarative.recIdxCtorB a h14 i

/-- the lifted telescope's `constsMemberFuel` decomposes into the field sweep
    and the family-application result check (the `vaTel` step, generic). -/
theorem recTelCm {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) (E' : ResolvedEnv) :
    constsMemberFuel E' (h14.fuelAt i + 1)
      (lift 0 ((a.constructorViews i).fields.length + 1 +
          a.constructors.length + a.family.indices.length)
        (ctorFieldTelescope (a.constructorViews i))) =
    ((a.constructorViews i).fields.all
      (constsMemberFuel E' (h14.fuelAt i + 1)) &&
      constsMemberFuel E' (h14.fuelAt i + 1)
        (foldApps (.const a.family.ref (policyFamilyLevels a.family))
          (policyParameterLocals (a.constructorViews i).parameters.length
            (a.constructorViews i).fields.length ++
            (a.constructorViews i).resultIndices))) := by
  rw [constsMemberFuel_lift]
  unfold ctorFieldTelescope
  rw [policyPi_eq_foldr, FunRecTyped.constsMemberFuel_foldr_pi]

/-- the family-application result check, discharged by the family head's
    non-transparency plus the bare-bvar parameter sweep and the already-leafed
    result-index sweep (the `vaRes` step, generic). -/
theorem recResCm {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    (a : RecursorEliminationAdmitted E r m) (h14 : IotaDescriptorClause E a)
    (i : Fin a.constructors.length) (E' : ResolvedEnv)
    (hfam : E'.members a.family.ref = some a.family.member)
    (hri : (a.constructorViews i).resultIndices.all
      (constsMemberFuel E' (h14.fuelAt i + 1)) = true) :
    constsMemberFuel E' (h14.fuelAt i + 1)
      (foldApps (.const a.family.ref (policyFamilyLevels a.family))
        (policyParameterLocals (a.constructorViews i).parameters.length
          (a.constructorViews i).fields.length ++
          (a.constructorViews i).resultIndices)) = true := by
  rw [FunRecTyped.constsMemberFuel_foldApps, List.all_append]
  simp only [Bool.and_eq_true]
  exact ⟨FunRecTyped.constsMemberFuel_famConst a hfam _ _,
    FunRecTyped.policyParameterLocals_all _ _ _ _, hri⟩

/-- one constructor's `recCtorCheckB` conjunct from its seven leaves (the
    `vaCtorB` step, generic). -/
theorem recCtorCheckB_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {h14 : IotaDescriptorClause E a}
    {i : Fin a.constructors.length}
    (hclosed : Rcic.Declarative.exprClosedAt 0 a.constructors[i.val].mtype = true)
    (hfE : (a.constructorViews i).fields.all
      (constsMemberFuel E (h14.fuelAt i + 1)) = true)
    (hriE : (a.constructorViews i).resultIndices.all
      (constsMemberFuel E (h14.fuelAt i + 1)) = true)
    (hfX : (a.constructorViews i).fields.all
      (constsMemberFuel (extendEnv E r m) (h14.fuelAt i + 1)) = true)
    (hriX : (a.constructorViews i).resultIndices.all
      (constsMemberFuel (extendEnv E r m) (h14.fuelAt i + 1)) = true)
    (hfamX : (extendEnv E r m).members a.family.ref = some a.family.member)
    (hscope : Rcic.Declarative.exprClosedAt (a.family.parameters.length + 1 +
        a.constructors.length + a.family.indices.length +
        (a.constructorViews i).fields.length)
      (descriptorSchema a h14 i) = true) :
    recCtorCheckB a h14 i = true := by
  unfold recCtorCheckB Rcic.Declarative.recIdxCtorB iotaWitnessStableB
  rw [recTelCm a h14 i E, recTelCm a h14 i (extendEnv E r m)]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨hclosed,
      ⟨⟨hfE, FunRecTyped.fieldBvars_all _ _ _⟩,
        ⟨hfE, recResCm a h14 i E a.family.present hriE⟩⟩⟩,
    ⟨⟨hfX, FunRecTyped.fieldBvars_all _ _ _⟩,
      ⟨hfX, recResCm a h14 i _ hfamX hriX⟩⟩⟩,
    hscope⟩

/-- `recIdxAdmittedTB` from its member-level leaves and the per-constructor
    `recCtorCheckB` family (the `vaRecIdxAdmittedB` step, generic). -/
theorem recIdxAdmittedB_of {E : ResolvedEnv} {r : Nat} {m : CheckedMember}
    {a : RecursorEliminationAdmitted E r m} {h14 : IotaDescriptorClause E a}
    (hfresh : (E.members r).isNone = true)
    (hclass : (match m.mclass with | .recursorM => true | _ => false) = true)
    (hmtype : Rcic.Declarative.exprClosedAt 0 m.mtype = true)
    (hctors : ∀ i : Fin a.constructors.length,
      recCtorCheckB a h14 i = true) :
    recIdxAdmittedTB a h14 = true := by
  unfold recIdxAdmittedTB
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hfresh, hclass⟩, hmtype⟩, ?_⟩
  rw [List.all_eq_true]
  intro j hj
  have hjlen : j < a.constructors.length := List.mem_range.mp hj
  rw [dif_pos hjlen]
  exact hctors ⟨j, hjlen⟩

/-- `xs.all f` from per-element leaves (the `List.all_eq_true` discharge at a
    concrete index, without re-evaluating the sweep). -/
theorem allB_of_each {α : Type} {xs : List α} {f : α → Bool}
    (h : ∀ k : Fin xs.length, f xs[k.val] = true) : xs.all f = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.all_cons, Bool.and_eq_true]
      exact ⟨h ⟨0, Nat.succ_pos _⟩,
        ih (fun ⟨k, hk⟩ => h ⟨k + 1, Nat.succ_lt_succ hk⟩)⟩

/-- `finAllB` from per-index leaves. -/
theorem finAllB_of_each {n : Nat} {f : (i : Nat) → i < n → Bool}
    (h : ∀ i : Fin n, f i.val i.isLt = true) : finAllB n f = true := by
  unfold finAllB
  rw [List.all_eq_true]
  intro j hj
  have hjlen : j < n := List.mem_range.mp hj
  rw [dif_pos hjlen]
  exact h ⟨j, hjlen⟩

/-! ### One-step `constsMemberFuel` constructors

`constsMemberFuel` on a transparent constant (e.g. slot 17's 64-byte digest
literal) expands the member body in one kernel pass, which exceeds the
deterministic step budget no matter how the sweep is split.  These lemmas let
a check be assembled node-by-node: each is a one-layer unfold plus a lookup
fact (`E.members r = some m`) that is itself a small `rfl`.  Fuel only
decrements through a transparent `const`'s body, so a generated proof tree
over a body whose inner constants are all non-transparent keeps fuel `n+1`
throughout. -/

theorem cmf_step_bvar {E : ResolvedEnv} {n i : Nat} :
    constsMemberFuel E (n+1) (.bvar i) = true := by
  simp only [constsMemberFuel]

theorem cmf_step_sort {E : ResolvedEnv} {n : Nat} {l : Level} :
    constsMemberFuel E (n+1) (.sort l) = true := by
  simp only [constsMemberFuel]

/-- Literal alias: `.lit t`'s expansion carries constants `{1}` (t = 0) or
    `{1, 2}` (t ≥ 1); each is checked the way `.const` is — the member lookup,
    plus a body check at one less fuel only when the member is transparent. -/
theorem cmf_step_lit {E : ResolvedEnv} {n t : Nat} {m1 m2 : CheckedMember}
    (hm1 : E.members 1 = some m1) (ht1 : transparent m1.mclass = false)
    (hm2 : E.members 2 = some m2) (ht2 : transparent m2.mclass = false) :
    constsMemberFuel E (n+1) (.lit t) = true := by
  cases t with
  | zero =>
      simp only [constsMemberFuel, hm1]
      rw [if_neg (by rw [ht1]; decide)]
  | succ _ =>
      simp only [constsMemberFuel, hm2]
      rw [if_neg (by rw [ht2]; decide)]
      simp only [hm1]
      rw [if_neg (by rw [ht1]; decide)]
      rfl

theorem cmf_step_app {E : ResolvedEnv} {n : Nat} {f a : Expr Nat}
    (hf : constsMemberFuel E (n+1) f = true)
    (ha : constsMemberFuel E (n+1) a = true) :
    constsMemberFuel E (n+1) (.app f a) = true := by
  simp only [constsMemberFuel]
  rw [hf, ha]
  rfl

theorem cmf_step_lam {E : ResolvedEnv} {n : Nat} {A b : Expr Nat}
    (hA : constsMemberFuel E (n+1) A = true)
    (hb : constsMemberFuel E (n+1) b = true) :
    constsMemberFuel E (n+1) (.lam A b) = true := by
  simp only [constsMemberFuel]
  rw [hA, hb]
  rfl

theorem cmf_step_pi {E : ResolvedEnv} {n : Nat} {A b : Expr Nat}
    (hA : constsMemberFuel E (n+1) A = true)
    (hb : constsMemberFuel E (n+1) b = true) :
    constsMemberFuel E (n+1) (.pi A b) = true := by
  simp only [constsMemberFuel]
  rw [hA, hb]
  rfl

theorem cmf_step_letE {E : ResolvedEnv} {n : Nat} {A v b : Expr Nat}
    (hA : constsMemberFuel E (n+1) A = true)
    (hv : constsMemberFuel E (n+1) v = true)
    (hb : constsMemberFuel E (n+1) b = true) :
    constsMemberFuel E (n+1) (.letE A v b) = true := by
  simp only [constsMemberFuel]
  rw [hA, hv, hb]
  rfl

/-- Non-transparent constant: the lookup plus the rigidity fact; the body is
    never consulted. -/
theorem cmf_step_const_ntrans {E : ResolvedEnv} {n r : Nat} {ls : List Level}
    {m : CheckedMember} (hm : E.members r = some m)
    (ht : transparent m.mclass = false) :
    constsMemberFuel E (n+1) (.const r ls) = true := by
  simp only [constsMemberFuel, hm, ht]
  rw [if_neg (by decide : ¬ (false = true))]

/-- Transparent constant: the lookup, transparency, and body facts, then the
    instantiated body's own (assembled) check at one less fuel. -/
theorem cmf_step_const_trans {E : ResolvedEnv} {n r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat} (hm : E.members r = some m)
    (ht : transparent m.mclass = true) (hb : m.body = some b)
    (h : constsMemberFuel E n (instantiateLevels ls b) = true) :
    constsMemberFuel E (n+1) (.const r ls) = true := by
  simp only [constsMemberFuel, hm, ht, hb]
  exact h

end Rcic.Scm.SrcG
