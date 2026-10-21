import rcic.RcicTypedCheck
import rcic.RcicTypedEnv
import rcic.RcicTypedIdxAdmitted
import rcic.RcicTypedScopeCheck
import rcic.RcicUntypedConvCollapse

/-!
# Curry exploit — the refusal tooth (step 2)

`Q : Prop` axiom at ref 0. `F : Sort 1` family at ref 1. Constructor `mk`
at ref 2 with field `Π (_ : .lit 0), .const 0 []`. `natExpand 0 = .const 1 []`,
so the field is `F → Q` semantically: a *negative* recursive field.

Step 1 — commit `c70920d66a` ("exploit(rcic): Curry counterexample
sealed"), against the pre-fix scans — showed the `.lit`-alias blind spot
was a soundness hole: `fieldAnalyze`'s occurrence scan treated `.lit` as
constant-free, recorded `.nonrecursive`, `EnvWfT.group` admitted the
group (`envWfEr : EnvWfT Er`), and the recursor's `.anySort` elimination
yielded a closed inhabitant of `Q` via Curry's paradox, axiom-free
(`[propext, Quot.sound]` only). Post-fix `envWfEr` cannot hold — the
group is refused — so the exploit revision lives at `c70920d66a`, not in
this file (`closedQ` below still shows the term-level derivation exists
in the *raw* environment).

Step 2 is the fix: every semantic occurrence/closure scanner now sees
through `.lit`/`natExpand` (`occursConst`, `containsFamilyFuel`,
`constsMemberFuel`/`ConstsMemberClosed`, `idxFamFreeAt`/`idxFamFreeLegacy`,
`ConstsIn`/`ConstsInA`, `constsBelow`, `noTransparentB`/`esize`). This file
now pins the refusal:

* `analyzed`/`analyzedC` — `fieldAnalyze` returns
  `.refused .negativeOccurrence` (the `F` in the field's inner domain is
  now seen), so `fieldShapesFuel` returns `none`;
* `ctorFieldsRefused`/`ctorFieldsRefusedC` — `CtorFieldsPermitted` is
  uninhabited for the canonical view;
* `ctorMember_not_admitted`/`recMember_not_admitted` — **no**
  `IndGroupAdmitted` exists for `mk` or `rec_F`, so `GroupMembersT.cons`
  cannot carry this group and `EnvWfT Er` is unprovable;
* `closedQ` — the Curry derivation still type-checks in the raw env,
  which is exactly why the environment side must refuse.
-/

namespace Rcic.ScopeCurryPin

open Rcic.Declarative
open Rcic.Declarative.UntypedConvCollapse

/- Q : Prop at ref 0; F : Sort 1 at ref 1; mk : (lit 0 → Q) → F at ref 2. -/

def qMem : CheckedMember := ⟨.axiomM, 0, .sort .zero, none⟩
def E0 : ResolvedEnv := extendEnv emptyEnv 0 qMem
def fMem : CheckedMember := ⟨.inductiveM, 0, .sort (.succ .zero), none⟩
def ES : ResolvedEnv := extendEnv E0 1 fMem

def fieldDom : Expr Nat := .pi (.lit 0) (.const 0 [])
def ctorTy : Expr Nat := .pi fieldDom (.const 1 [])
def ctorMember : CheckedMember := ⟨.constructorM, 0, ctorTy, none⟩

def showE : Expr Nat → String
  | .bvar i => s!"#{i}"
  | .sort .zero => "S0"
  | .sort (.succ .zero) => "S1"
  | .sort (.succ (.succ .zero)) => "S2"
  | .sort (.param i) => s!"u{i}"
  | .sort (.imax a b) => s!"(imax {showE (.sort a)} {showE (.sort b)})"
  | .sort _ => "S?"
  | .const r _ => s!"c{r}"
  | .app f x => s!"({showE f} {showE x})"
  | .lam a b => s!"(λ {showE a}. {showE b})"
  | .pi a b => s!"(Π {showE a}. {showE b})"
  | .letE _ _ _ => "let"
  | .lit n => s!"lit{n}"

#eval showE fieldDom
#eval showE ctorTy

def litTyU : HasTy ES 0 [] (.lit 0) (.sort (.succ .zero)) :=
  .lit [] 0 _ (.const [] 1 [] fMem rfl rfl (fun _ h => nomatch h))

def fieldTyU : HasTy ES 0 [] fieldDom (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] (.lit 0) (.succ .zero) (.const 0 []) .zero litTyU
    (.const _ 0 [] qMem rfl rfl (fun _ h => nomatch h))

def family : PolicyFamilyView ES where
  ref := 1
  member := fMem
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def ctorView : PolicyConstructorView ES family ctorMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [fieldDom]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .imax (.succ .zero) .zero
    bounded := fun _ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => by simpa [policyPrefixContext] using fieldTyU
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

/-- The occurrence scan now sees `const 1` through `lit 0`: the field's
inner domain contains the family in negative position and is refused. -/
theorem analyzed :
    fieldAnalyze ES 8 1 0 0 0 0 fieldDom = .refused .negativeOccurrence := rfl

theorem shapesRefused :
    fieldShapesFuel ES 8 1 0 0 0 0 [fieldDom] = none := rfl

def fieldRefused : FieldRefused ES 1 0 0 0 0 fieldDom .negativeOccurrence :=
  ⟨8, analyzed⟩

/-- The positivity gate `h08` of `IndGroupAdmitted.constructor` is
uninhabited for the canonical view. -/
theorem ctorFieldsRefused : ¬ CtorFieldsPermitted ctorView := by
  intro h
  obtain ⟨_, hp⟩ := h ⟨0, by decide⟩
  exact FieldPermitted.not_refused hp fieldRefused

theorem univOk : FieldUniverseAdmitted ctorView := fun j =>
  match j with
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, by
      intro ρ x y hx hy
      simp [eval] at hx hy
      omega⟩

theorem famRef : memberFamRef ctorMember = some 1 := rfl

theorem membersS : ES.members = fun n =>
    if n = 1 then some fMem else if n = 0 then some qMem else none := rfl

theorem before : CtorBeforeRecursors ES ctorMember := by
  refine ⟨1, famRef, ?_⟩
  intro rr rm hm hk _
  rw [membersS] at hm
  by_cases h1 : rr = 1
  · simp [h1] at hm
    cases hm
    cases hk
  · by_cases h0 : rr = 0
    · simp [h1, h0] at hm
      cases hm
      cases hk
    · simp [h1, h0] at hm

theorem contig : CtorContiguous ES 2 ctorMember := by
  refine ⟨1, famRef, Nat.one_lt_two, ?_, ?_⟩
  · intro c hl hr
    match c with
    | 0 => exact False.elim (Nat.not_lt_zero 1 hl)
    | 1 => exact False.elim (Nat.lt_irrefl 1 hl)
    | n + 2 => exact False.elim (absurd hr (Nat.not_lt.mpr (Nat.le_add_left 2 n)))
  · intro c h
    rcases h with ⟨cm, hm, hc, _⟩
    rw [membersS] at hm
    match c with
    | 0 => cases hm; cases hc
    | 1 => cases hm; cases hc
    | _ + 2 => cases hm

def minorOpt : Option (Expr Nat) :=
  minorFromTelescope ES 8 0 (.bvar 0) (.const 2 [])
    [.nonrecursive] (lift 0 1 (ctorFieldTelescope ctorView))

#eval minorOpt.map showE

def minorTy : Expr Nat :=
  match minorOpt with
  | some m => m
  | none => .sort .zero

theorem minorTy_spec : minorOpt = some minorTy := rfl

def Ec : ResolvedEnv := extendEnv ES 2 ctorMember

def familyC : PolicyFamilyView Ec where
  ref := 1
  member := fMem
  present := rfl
  hasClass := rfl
  parameters := []
  indices := []
  resultLevel := .succ .zero
  resultBounded := rfl
  storedType := rfl
  domainsTyped := .empty _ _

def fieldTyUC : HasTy Ec 0 [] fieldDom (.sort (.imax (.succ .zero) .zero)) :=
  .pi [] (.lit 0) (.succ .zero) (.const 0 []) .zero
    (.lit [] 0 _ (.const [] 1 [] fMem rfl rfl (fun _ h => nomatch h)))
    (.const _ 0 [] qMem rfl rfl (fun _ h => nomatch h))

def ctorViewC : PolicyConstructorView Ec familyC ctorMember where
  hasClass := rfl
  arity := rfl
  parameters := []
  fields := [fieldDom]
  resultIndices := []
  parameterCount := rfl
  indexCount := rfl
  storedType := rfl
  domainsTyped := {
    levels := fun _ => .imax (.succ .zero) .zero
    bounded := fun _ => rfl
    hasType := fun j =>
      match j with
      | ⟨0, _⟩ => by simpa [policyPrefixContext] using fieldTyUC
  }
  parameterMirrors := fun i => i.elim0
  noFamilyInIndices := fun _ h => nomatch h

def recTyRaw : Expr Nat := policyRecursorType familyC [minorTy] .anySort
def recMember : CheckedMember := ⟨.recursorM, 1, recTyRaw, none⟩

#eval showE recTyRaw
#eval showE minorTy
#eval (inferT Ec 1 [] recTyRaw).map showE
#eval (groupSkel? synChecker E0 8 1 fMem [(2, ctorMember)] recMember 0).isSome

abbrev fieldUniv : Level := .imax (.succ .zero) .zero
abbrev ctorUniv : Level := .imax fieldUniv (.succ .zero)

def litTyTS : HasTyT ES 0 [] (.lit 0) (.sort (.succ .zero)) :=
  .lit [] 0 _ (.const [] 1 [] fMem rfl rfl rfl)

def fieldTyTS : HasTyT ES 0 [] fieldDom (.sort fieldUniv) :=
  .pi [] (.lit 0) (.succ .zero) (.const 0 []) .zero litTyTS
    (.const _ 0 [] qMem rfl rfl rfl)

def ctorTyT : HasTyT ES 0 [] ctorTy (.sort ctorUniv) :=
  .pi [] fieldDom fieldUniv (.const 1 []) (.succ .zero) fieldTyTS
    (.const _ 1 [] fMem rfl rfl rfl)

def fieldTyTC : HasTyT Ec 0 [] fieldDom (.sort fieldUniv) :=
  .pi [] (.lit 0) (.succ .zero) (.const 0 []) .zero
    (.lit [] 0 _ (.const [] 1 [] fMem rfl rfl rfl))
    (.const _ 0 [] qMem rfl rfl rfl)

theorem ctorFieldsTyped : CtorTypedT ctorView := by
  refine ⟨?_, fun i => i.elim0⟩
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨fieldTyTS⟩

theorem ctorFieldsTypedC : CtorTypedT ctorViewC := by
  refine ⟨?_, fun i => i.elim0⟩
  intro i
  match i with
  | ⟨0, _⟩ => exact ⟨fieldTyTC⟩

theorem analyzedC :
    fieldAnalyze Ec 8 1 0 0 0 0 fieldDom = .refused .negativeOccurrence := rfl

theorem shapesRefusedC :
    fieldShapesFuel Ec 8 1 0 0 0 0 [fieldDom] = none := rfl

def fieldRefusedC : FieldRefused Ec 1 0 0 0 0 fieldDom .negativeOccurrence :=
  ⟨8, analyzedC⟩

theorem ctorFieldsRefusedC : ¬ CtorFieldsPermitted ctorViewC := by
  intro h
  obtain ⟨_, hp⟩ := h ⟨0, by decide⟩
  exact FieldPermitted.not_refused hp fieldRefusedC

theorem univOkC : FieldUniverseAdmitted ctorViewC := fun j =>
  match j with
  | ⟨0, _⟩ => Or.inr ⟨uniformType_succ_zero, by
      intro ρ x y hx hy
      simp [eval] at hx hy
      omega⟩

def famAdmitted : IndGroupAdmitted E0 1 fMem :=
  .family rfl family rfl rfl (Or.inr uniformType_succ_zero)

theorem famTyped : IndGroupTypedT famAdmitted := fun i => i.elim0

def famSortTy : HasTyT E0 0 [] fMem.mtype (.sort (.succ (.succ .zero))) :=
  .sort [] (.succ .zero)

def Er : ResolvedEnv := extendEnv Ec 3 recMember

theorem membersC : Ec.members = fun n =>
    if n = 2 then some ctorMember
    else if n = 1 then some fMem else if n = 0 then some qMem else none := rfl

abbrev recUniv : Level :=
  .imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.imax (.imax (.succ .zero) .zero) (.param 0))
      (.imax (.succ .zero) (.param 0)))

theorem recInf : inferT Ec 1 [] recTyRaw = some (.sort recUniv) := rfl

/-- The recursor signature itself still infers a sort — what the refusal
removes is the *admission* evidence, not the signature's typability. -/
def recTyT : HasTyT Ec 1 [] recTyRaw (.sort recUniv) := hasTyT_of_inferT recInf

def envQ : EnvWfT E0 :=
  .axiom emptyEnv 0 (.sort .zero) (.succ .zero) .empty rfl
    (.sort [] .zero) (fun _ => rfl) rfl

/-! ### Group-level refusal: no `IndGroupAdmitted` exists at all

`CtorFieldsPermitted` on the *canonical* view is already uninhabited; the
following inversions show every possible view is forced to the same
fields list, so the positivity gate fails for every admission attempt. -/

/-- The family view in `ES` is forced to ref 1 / `fMem`: ref 0 is an
axiom and no other member exists. -/
theorem family_forced_ES (view : PolicyFamilyView ES) :
    view.ref = 1 ∧ view.member = fMem := by
  have hmem := view.present
  rw [membersS] at hmem
  dsimp only at hmem
  by_cases h1 : view.ref = 1
  · rw [if_pos h1] at hmem
    exact ⟨h1, (Option.some.inj hmem).symm⟩
  · by_cases h0 : view.ref = 0
    · rw [if_neg h1, if_pos h0] at hmem
      have hm : view.member = qMem := (Option.some.inj hmem).symm
      nomatch (hm ▸ view.hasClass)
    · rw [if_neg h1, if_neg h0] at hmem
      nomatch hmem

/-- The family view in `Ec` is likewise forced to ref 1 / `fMem`. -/
theorem family_forced_Ec (view : PolicyFamilyView Ec) :
    view.ref = 1 ∧ view.member = fMem := by
  have hmem := view.present
  rw [membersC] at hmem
  dsimp only at hmem
  by_cases h2 : view.ref = 2
  · rw [if_pos h2] at hmem
    have hm : view.member = ctorMember := (Option.some.inj hmem).symm
    nomatch (hm ▸ view.hasClass)
  · by_cases h1 : view.ref = 1
    · rw [if_neg h2, if_pos h1] at hmem
      exact ⟨h1, (Option.some.inj hmem).symm⟩
    · by_cases h0 : view.ref = 0
      · rw [if_neg h2, if_neg h1, if_pos h0] at hmem
        have hm : view.member = qMem := (Option.some.inj hmem).symm
        nomatch (hm ▸ view.hasClass)
      · rw [if_neg h2, if_neg h1, if_neg h0] at hmem
        nomatch hmem

/-- A family view of `fMem` has no parameters and no indices: its stored
type is a `Sort`, and `policyPi` of any nonempty telescope is a `pi`. -/
theorem family_flat (view : PolicyFamilyView ES) (hm : view.member = fMem) :
    view.parameters = [] ∧ view.indices = [] := by
  have hst := view.storedType
  rw [hm] at hst
  cases hpi : view.parameters ++ view.indices with
  | nil => simpa using hpi
  | cons a rest =>
      rw [hpi] at hst
      simp only [policyPi] at hst
      nomatch hst

/-- The same flattening in `Ec`. -/
theorem family_flat_Ec (view : PolicyFamilyView Ec) (hm : view.member = fMem) :
    view.parameters = [] ∧ view.indices = [] := by
  have hst := view.storedType
  rw [hm] at hst
  cases hpi : view.parameters ++ view.indices with
  | nil => simpa using hpi
  | cons a rest =>
      rw [hpi] at hst
      simp only [policyPi] at hst
      nomatch hst

/-- A `foldApps` whose head is not a `pi` never yields a `pi`: the
accumulator only produces `f` itself or an `.app` spine. -/
theorem pi_ne_foldApps {A B : Expr Nat} :
    ∀ (xs : List (Expr Nat)) (f : Expr Nat), (∀ C D, f ≠ .pi C D) →
      .pi A B ≠ foldApps f xs
  | [], f, hf => fun h => hf _ _ h.symm
  | x :: xs, f, _ => pi_ne_foldApps xs (.app f x) (fun _ _ h => nomatch h)

/-- Every constructor view over a member whose stored type is
`Π (_ : fieldDom), F` is forced to `fields = [fieldDom]`:
`parameterCount` empties the parameter list when the family has none,
and `storedType` then pins the single `pi` domain. -/
theorem ctorView_fields {E : ResolvedEnv} {fam : PolicyFamilyView E}
    {m : CheckedMember} (hfp : fam.parameters = [])
    (view : PolicyConstructorView E fam m)
    (hm : m.mtype = .pi fieldDom (.const 1 [])) :
    view.fields = [fieldDom] := by
  have hparams : view.parameters = [] := by
    have hc := view.parameterCount
    rw [hfp] at hc
    simpa using hc
  have hst : .pi fieldDom (.const 1 []) =
      policyPi (view.parameters ++ view.fields) _ := hm ▸ view.storedType
  rw [hparams, List.nil_append] at hst
  cases hfl : view.fields with
  | nil =>
      rw [hfl] at hst
      exact absurd hst
        (pi_ne_foldApps _ (.const fam.ref (policyFamilyLevels fam))
          (fun _ _ h => nomatch h))
  | cons f rest =>
      rw [hfl] at hst
      simp only [policyPi] at hst
      injection hst with hf1 hf2
      cases rest with
      | nil => rw [← hf1]
      | cons g rest' =>
          simp only [policyPi] at hf2
          nomatch hf2

/-- `mk` cannot be admitted: `.family`/`.recursor` die on the member
class, `.constructor` dies on `CtorFieldsPermitted`, and a spurious
`.recursor` dies because `ctorTy`'s first domain is `Π (_ : lit 0), Q`,
never the canonical motive type `Π (_ : const 1 _), Sort _`. -/
theorem ctorMember_not_admitted : IndGroupAdmitted ES 2 ctorMember → False := by
  intro h
  cases h with
  | family _ view _ hm _ =>
      have hc : ctorMember.mclass = .inductiveM := hm ▸ view.hasClass
      nomatch hc
  | constructor fam' view _ _ _ _ h08 =>
      obtain ⟨hfr, hfm⟩ := family_forced_ES fam'
      obtain ⟨hfp, hfi⟩ := family_flat fam' hfm
      have hfl := ctorView_fields hfp view rfl
      simp only [CtorFieldsPermitted] at h08
      have hmem : fieldDom ∈ view.fields := by rw [hfl]; exact .head []
      obtain ⟨n', hn', hval⟩ := List.mem_iff_getElem.mp hmem
      have hn0 : n' = 0 := by
        rw [hfl] at hn'; simp only [List.length_cons, List.length_nil] at hn'; omega
      subst hn0
      obtain ⟨_, fuel, indices, hp⟩ := h08 ⟨0, hn'⟩
      rw [hfr, hfm, hfp, hfi] at hp
      rw [hval] at hp
      exact FieldPermitted.not_refused ⟨fuel, indices, hp⟩ fieldRefused
  | recursor a _ _ _ _ _ _ =>
      obtain ⟨hfr, hfm⟩ := family_forced_ES a.family
      obtain ⟨hfp, hfi⟩ := family_flat a.family hfm
      have hrr := a.recursorRef
      rw [hfr] at hrr
      have hlen : a.constructors.length = 0 := by omega
      have hml : a.minorTypes = [] := by
        have hc' := a.minorCount
        rw [hlen] at hc'
        simpa using hc'
      have hrt := a.recursorType
      rw [hml] at hrt
      simp only [ctorMember, ctorTy, fieldDom, policyRecursorType,
        policyMotiveType, policyMotiveLevel, policyPi, policyLocals,
        policyParameterLocals, policyFamilyLevels, foldApps, fMem,
        List.range, List.map, List.mapIdx, List.reverse, List.append,
        List.nil_append, hfp, hfi, hfr, hfm] at hrt
      injection hrt with hd _
      injection hd with hl _
      nomatch hl

/-- `rec_F` cannot be admitted either: `.family` and `.constructor` die on
the member class; `.recursor` forces `constructors = [ctorMember]` via
`recursorRef`, and its per-constructor `CtorFieldsPermitted` is the same
uninhabited positivity gate. -/
theorem recMember_not_admitted : IndGroupAdmitted Ec 3 recMember → False := by
  intro h
  cases h with
  | family _ view _ hm _ =>
      have hc : recMember.mclass = .inductiveM := hm ▸ view.hasClass
      nomatch hc
  | constructor _ view _ _ _ _ _ =>
      nomatch view.hasClass
  | recursor a _ _ _ h08 _ _ =>
      obtain ⟨hfr, hfm⟩ := family_forced_Ec a.family
      obtain ⟨hfp, hfi⟩ := family_flat_Ec a.family hfm
      have hrr := a.recursorRef
      rw [hfr] at hrr
      cases hcl : a.constructors with
      | nil =>
          rw [hcl] at hrr
          simp only [List.length] at hrr
          omega
      | cons c0 rest =>
          cases rest with
          | nil =>
              have h0 : 0 < a.constructors.length := by
                have h1 : a.constructors.length = 1 := by simp [hcl]
                omega
              have hcp := a.constructorsPresent ⟨0, h0⟩
              rw [hfr, membersC] at hcp
              dsimp only at hcp
              have hc0 : a.constructors[(⟨0, h0⟩ : Fin _).val] = ctorMember :=
                (Option.some.inj hcp).symm
              have hm : a.constructors[(⟨0, h0⟩ : Fin _).val].mtype =
                  .pi fieldDom (.const 1 []) :=
                congrArg CheckedMember.mtype hc0
              have hfl := ctorView_fields hfp (a.constructorViews ⟨0, h0⟩) hm
              have h08v := h08 ⟨0, h0⟩
              simp only [CtorFieldsPermitted] at h08v
              have hmem : fieldDom ∈ (a.constructorViews ⟨0, h0⟩).fields := by
                rw [hfl]; exact .head []
              obtain ⟨n', hn', hval⟩ := List.mem_iff_getElem.mp hmem
              have hn0 : n' = 0 := by
                rw [hfl] at hn'
                simp only [List.length_cons, List.length_nil] at hn'
                omega
              subst hn0
              obtain ⟨_, fuel, indices, hp⟩ := h08v ⟨0, hn'⟩
              rw [hfr, hfm, hfp, hfi] at hp
              rw [hval] at hp
              exact FieldPermitted.not_refused ⟨fuel, indices, hp⟩ fieldRefusedC
          | cons c1 rest' =>
              rw [hcl] at hrr
              simp only [List.length_cons] at hrr
              omega

theorem readerRefusesField :
    fieldsCheckB synChecker E0 0 (fun _ => .sort (.succ .zero)) [] 0
      [.plain fieldDom fieldUniv] [] = false := rfl

theorem scopeRefusesGroup :
    groupSkel? synChecker E0 8 1 fMem [(2, ctorMember)] recMember 0 = none := rfl

/-! ## The Curry derivation

`notF := λ (f : F). rec_F (λ _. Q) (λ g. g f) f`, `t := notF (mk notF)`.
The recursor at `[.zero]` instantiates `Π (M : Π (_ : F), Sort 0)
  (m : Π (g : Π (_ : lit 0), Q), M (mk g)) (x : F), M x`. -/

/-- `λ (_ : F). Q`, the constant `Q`-valued motive. -/
def mot : Expr Nat := .lam (.const 1 []) (.const 0 [])

/-- Inside `λ f`: `λ (g : Π (_ : lit 0), Q). g f`. -/
def minB : Expr Nat := .lam fieldDom (.app (.bvar 0) (.bvar 1))

/-- `λ (f : F). rec_F (λ _. Q) (λ g. g f) f`. -/
def notF : Expr Nat :=
  .lam (.const 1 [])
    (.app (.app (.app (.const 3 [.zero]) mot) minB) (.bvar 0))

/-- `notF (mk notF) : Q`. -/
def curryTy : Expr Nat := .app notF (.app (.const 2 []) notF)

def fTyEr : HasTyT Er 0 [] (.const 1 []) (.sort (.succ .zero)) :=
  .const [] 1 [] fMem rfl rfl rfl

def litTyEr : HasTyT Er 0 [] (.lit 0) (.sort (.succ .zero)) :=
  .lit [] 0 _ fTyEr

def fieldTyEr : HasTyT Er 0 [] fieldDom (.sort fieldUniv) :=
  .pi [] (.lit 0) (.succ .zero) (.const 0 []) .zero litTyEr
    (.const _ 0 [] qMem rfl rfl rfl)

/-- The lit-alias conversion: `const 1 ≡ lit 0` at `Sort 1`. -/
def constLitConv (Γ : LCtx) :
    ConvT Er 0 Γ (.const 1 []) (.lit 0) (.sort (.succ .zero)) :=
  .symm Γ (.lit 0) (.const 1 []) (.sort (.succ .zero))
    (.lit Γ 0 (.const 1 []) (.sort (.succ .zero)) (.of 0)
      (.const Γ 1 [] fMem rfl rfl rfl))

/-- `f : F` converts to `f : lit 0`. -/
def fLitTy (Γ : LCtx) (f : Expr Nat) (hf : HasTyT Er 0 Γ f (.const 1 [])) :
    HasTyT Er 0 Γ f (.lit 0) :=
  .conv _ _ _ _ _ hf (constLitConv Γ)

def motTy0 : HasTyT Er 0 [] mot (.pi (.const 1 []) (.sort .zero)) :=
  .lam [] (.const 1 []) (.succ .zero) (.const 0 []) (.sort .zero) fTyEr
    (.const _ 0 [] qMem rfl rfl rfl)

/-- `mk`'s full typing in `Er`. -/
def mkTy (Γ : LCtx) : HasTyT Er 0 Γ (.const 2 [])
    (.pi fieldDom (.const 1 [])) :=
  .const Γ 2 [] ctorMember rfl rfl rfl

/-- `notF`'s body typing in the `[f : F]` context: `rec mot minB f` at
`app mot f`, β-converted to `Q = const 0`. -/
def notFBody :
    HasTyT Er 0 [.assumption (.const 1 [])]
      (.app (.app (.app (.const 3 [.zero]) mot) minB) (.bvar 0))
      (.const 0 []) := by
  -- f : F at bvar 0
  have hf : HasTyT Er 0 [.assumption (.const 1 [])] (.bvar 0) (.const 1 []) :=
    .bvar _ 0 _ rfl
  -- g : fieldDom at bvar 0 in Γmin ; f : F at bvar 1
  have hg : HasTyT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.bvar 0) fieldDom := .bvar _ 0 _ rfl
  have hfG : HasTyT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.bvar 1) (.const 1 []) := .bvar _ 1 _ rfl
  -- f converted to `lit 0`, then `g f : Q`
  have hfLit : HasTyT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.bvar 1) (.lit 0) :=
    .conv _ (.bvar 1) (.const 1 []) (.lit 0) (.succ .zero) hfG (constLitConv _)
  have hgf : HasTyT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.app (.bvar 0) (.bvar 1)) (.const 0 []) :=
    .app _ (.bvar 0) (.bvar 1) (.lit 0) (.const 0 []) hg hfLit
  -- fieldDom : sort fieldUniv, in the `[f]` context
  have hfld : HasTyT Er 0 [.assumption (.const 1 [])] fieldDom
      (.sort fieldUniv) :=
    .pi _ (.lit 0) (.succ .zero) (.const 0 []) .zero
      (.lit _ 0 _ (.const _ 1 [] fMem rfl rfl rfl))
      (.const _ 0 [] qMem rfl rfl rfl)
  -- minB : Π (g : fieldDom), Q — the `lam` typing
  have hminB0 : HasTyT Er 0 [.assumption (.const 1 [])] minB
      (.pi fieldDom (.const 0 [])) :=
    .lam _ fieldDom fieldUniv (.app (.bvar 0) (.bvar 1)) (.const 0 [])
      hfld hgf
  -- `const 0 ≡ app mot (mk g)` under the field binder, via β
  have hmk : HasTyT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.app (.const 2 []) (.bvar 0)) (.const 1 []) :=
    .app _ (.const 2 []) (.bvar 0) fieldDom (.const 1 []) (mkTy _) hg
  have hbeta : ConvT Er 0 [.assumption fieldDom, .assumption (.const 1 [])]
      (.app mot (.app (.const 2 []) (.bvar 0))) (.const 0 []) (.sort .zero) :=
    .beta _ (.const 1 []) (.const 0 []) (.app (.const 2 []) (.bvar 0))
      (.sort .zero) (.succ .zero)
      (.const _ 1 [] fMem rfl rfl rfl)
      (.const _ 0 [] qMem rfl rfl rfl) hmk
  -- conv `Π g:fieldDom, Q ≡ Π g:fieldDom, app mot (mk g)`
  have hdom : ConvT Er 0 [.assumption (.const 1 [])] fieldDom fieldDom
      (.sort fieldUniv) :=
    .refl _ fieldDom (.sort fieldUniv) hfld
  have hpi : ConvT Er 0 [.assumption (.const 1 [])]
      (.pi fieldDom (.const 0 []))
      (.pi fieldDom (.app mot (.app (.const 2 []) (.bvar 0))))
      (.sort (.imax fieldUniv .zero)) :=
    .pi _ fieldDom fieldDom (.const 0 [])
      (.app mot (.app (.const 2 []) (.bvar 0))) fieldUniv .zero hdom
      (.symm _ _ _ _ hbeta)
  have hminB : HasTyT Er 0 [.assumption (.const 1 [])] minB
      (.pi fieldDom (.app mot (.app (.const 2 []) (.bvar 0)))) :=
    .conv _ minB (.pi fieldDom (.const 0 [])) _ _
      hminB0 hpi
  -- the recursor application
  have hrecT : HasTyT Er 0 [.assumption (.const 1 [])] (.const 3 [.zero])
      (instantiateLevels [.zero] recTyRaw) :=
    .const _ 3 [.zero] recMember rfl rfl rfl
  have happ1 := HasTyT.app _ (.const 3 [.zero]) mot _ _ hrecT
    (.lam _ (.const 1 []) (.succ .zero) (.const 0 []) (.sort .zero)
      (.const _ 1 [] fMem rfl rfl rfl)
      (.const _ 0 [] qMem rfl rfl rfl))
  have happ2 := HasTyT.app _ _ minB _ _ happ1 hminB
  have happ3 := HasTyT.app _ _ (.bvar 0) _ _ happ2 hf
  -- `app mot f ≡ Q` by β
  have hbetaF : ConvT Er 0 [.assumption (.const 1 [])] (.app mot (.bvar 0))
      (.const 0 []) (.sort .zero) :=
    .beta _ (.const 1 []) (.const 0 []) (.bvar 0) (.sort .zero)
      (.succ .zero) (.const _ 1 [] fMem rfl rfl rfl)
      (.const _ 0 [] qMem rfl rfl rfl) hf
  exact .conv _ _ _ (.const 0 []) .zero happ3 hbetaF

/-- `notF : F → Q`. -/
def notFTy : HasTyT Er 0 [] notF (.pi (.const 1 []) (.const 0 [])) :=
  .lam [] (.const 1 []) (.succ .zero) _ (.const 0 []) fTyEr notFBody

/-- `notF` converts to `fieldDom = Π (_ : lit 0), Q`. -/
def notFAsField : HasTyT Er 0 [] notF fieldDom := by
  have hdom : ConvT Er 0 [] (.const 1 []) (.lit 0) (.sort (.succ .zero)) :=
    constLitConv []
  have hcod : ConvT Er 0 [.assumption (.const 1 [])] (.const 0 [])
      (.const 0 []) (.sort .zero) :=
    .refl _ (.const 0 []) (.sort .zero)
      (.const _ 0 [] qMem rfl rfl rfl)
  have hpi : ConvT Er 0 [] (.pi (.const 1 []) (.const 0 []))
      (.pi (.lit 0) (.const 0 [])) (.sort fieldUniv) :=
    .pi [] (.const 1 []) (.lit 0) (.const 0 []) (.const 0 [])
      (.succ .zero) .zero hdom hcod
  exact .conv [] notF (.pi (.const 1 []) (.const 0 [])) fieldDom fieldUniv
    notFTy hpi

/-- `mk notF : F`. -/
def mkNotFTy : HasTyT Er 0 [] (.app (.const 2 []) notF) (.const 1 []) :=
  .app [] (.const 2 []) notF fieldDom (.const 1 []) (mkTy []) notFAsField

/-- The exploit: a closed inhabitant of the arbitrary axiom `Q : Prop`. -/
def closedQ : HasTyT Er 0 [] curryTy (.const 0 []) :=
  .app [] notF (.app (.const 2 []) notF) (.const 1 []) (.const 0 [])
    notFTy mkNotFTy

#print axioms notFTy
#print axioms closedQ



#print axioms notFBody
#print axioms constLitConv
#print axioms notFAsField
#print axioms mkNotFTy
#print axioms mkTy
#print axioms fieldRefused
#print axioms ctorFieldsRefused
#print axioms fieldRefusedC
#print axioms ctorFieldsRefusedC
#print axioms ctorMember_not_admitted
#print axioms recMember_not_admitted
#print axioms readerRefusesField
#print axioms scopeRefusesGroup
end Rcic.ScopeCurryPin
