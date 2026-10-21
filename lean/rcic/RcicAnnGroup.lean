import rcic.RcicAnnLevelIrr
import rcic.RcicUniverseClass

/-!
# M2-f (4a) — the group's views: a family and its constructors, in the base scope

05 §1 admits an inductive group as ONE atomic extension (the family, its constructors, then
the derived recursor), with three private scopes (§4): the family header in the base
environment (HeaderScope), the constructors in the base plus the provisional family
(ConstructorScope). The families' clause of the relation (`TyKA.fam`) reads, at a carrier, the
FAMILY-FREE parts of the constructors — plain field domains, recursive fields' indices, result
indices — under substitutions of related values; the environment discharge has only the base's
clauses at the group's step, and a valid substitution covers every context variable (M2-f
(4a)-0, README). So the group is stated through VIEWS whose family-free parts live in the PLAIN
context (the parameters, then the earlier plain fields) and are typed in the base environment:

* `FamViewA`: parameters and indices with their sorts, the result sort; the family's stored
  type is the telescope BUILT from them (`piTelA`); the parameter count is the declared one,
  `nparamsA`; the result profile 05 §5 (`UniformProp ∨ UniformType`).
* `CtorViewA`: the parameter mirrors, typed-convertible to the family's parameters (05 §6.1);
  the fields as `FieldA.plain D u` (domain and sort, plain context) or `FieldA.drec idx`
  (indices, plain context); the result indices (plain context); the stored type BUILT from them
  (`ctorTypeA`): mirrors, then the fields — plain domains carried into the full context past
  the recursive positions, recursive domains `F canonLevels (exact parameter locals ++ idx)` —
  then `F canonLevels (exact parameter locals ++ res)`. 05 §6.2–3/5 and §8's recursive shape
  hold by construction. Each plain domain, each recursive index list (along the family's index
  telescope) and the result index list typed in the base environment (`FieldsTyA`); field
  universes 05 §7.

THE BUILDER'S LAWS (§2b–§2d). Applying arguments walks a built constructor type as a state
machine over the parameter locals and the plain substitution: a plain field's argument extends
the substitution, a recursive field's is dropped from it, the parameter locals stay exact
(`applyTelA_ctorTypeA_params`: at the parameters `ps` the state is `(ps, consListA ps id)`;
`applyTelA_ctorTypeA`: after all the fields the result is `F ls (ps ++ res[plain args])`).
Level instantiation passes through the builder (`instantiateLevelsA_ctorTypeA`), the canonical
vector instantiating to the given list (`canonLevelsA_instLevel`). Through erasure, the built
type reads back the view's shapes when the fields are free of the family
(`ctorShapesA_ctorTypeA`), its kinds where no field is function-recursive (`ctorKindsA_ctorTypeA`),
and its result is headed by the family (`memberFamRefA`). A view typed
in a base where the family is fresh is free of it (`FieldsTyA.freeOf`), so at a group
constructor the `ctorShapesA` ι and the relation read and the `memberFamRefA` are the view's
(`CtorViewA.shapes`, `CtorViewA.famRef`; R-NoFunRec-1 step 1 (1c-γ)), and the `ctorKindsA` that serves the
correspondence with `main` is the view's (`CtorViewA.kinds`), and the instantiated telescopes at the
carrier's parameters are the views' (`FamViewA.applyTel_params`, `CtorViewA.applyTel_params`).

A function-recursive field (`FieldA.frec`, R-NoFunRec-1 step 1 (1c)) is a Π-telescope of inner binders
ending in `F canonLevels (exact parameter locals ++ idx)`: the field telescope at the inner binders read
as plain fields (`frecDomA_eq`). Through erasure it reads back its shape, `recursive` at its inner
binders' count (`fieldShapesE_ctorFieldsA`), and no kind: the kinds read back only where no field is
function-recursive (`ctorKindsA_ctorTypeA`). `FieldsTyA` types it as its domain reads: the inner binders
as plain fields in the plain context, ending in the indices along the index telescope past them. A view
carries no restriction on its fields (R-NoFunRec-1 step 1 (1c-ε3)): the erasure and bridge consumers read
that no field is function-recursive from the environment (`EnvNoFunA`, carried by `AnnEnvA`).
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-! ## (1) telescopes built from domains -/

/-- a Π-telescope over annotated domains ending in `B : Sort w`; each binder's codomain
    annotation is the sort of the rest (`imax`), and the telescope's sort is returned. -/
def piTelA : List (ExprA × Level) → ExprA → Level → ExprA × Level
  | [], B, w => (B, w)
  | (D, u) :: ds, B, w =>
      let r := piTelA ds B w
      (.pi D u r.1 r.2, .imax u r.2)

/-- a telescope's domains as a context: the earliest outermost (innermost first). -/
def telCtxA (ds : List (ExprA × Level)) : LCtxA :=
  (ds.map fun d => LocalDeclA.assumption d.1).reverse

/-- the parameter locals right after `np` parameter binders, outermost parameter first. -/
def paramLocalsA : Nat → List ExprA
  | 0 => []
  | n + 1 => .bvar n :: paramLocalsA n

/-- the family's canonical universe vector (05 §2). -/
def canonLevelsA (n : Nat) : List Level := (List.range n).map Level.param

/-! ## (2) constructor fields and the built constructor type -/

/-- a constructor field, in the PLAIN context (the parameters and the earlier plain fields):
    a plain field's domain and sort, a directly recursive field's indices, or a FUNCTION-RECURSIVE
    field's inner binders and indices (R-NoFunRec-1 step 1 (1c)): `B : Sort uB`, then `Bs`, each in the
    plain context extended by the earlier inner binders, and the indices in the plain context extended
    by all of them. The first inner binder is explicit, so `drec` is the only directly recursive field. -/
inductive FieldA : Type
  | plain (D : ExprA) (u : Level)
  | drec (idx : List ExprA)
  | frec (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA)
  | drecD (D : ExprA) (idx : List ExprA)

/-- the kind ι's correspondence with `main` reads (`ctorKindsA`, through erasure). `main` reads no kind
    at a function-recursive field; there `kind` is `directRec`, and every law reading kinds assumes a
    field that is not function-recursive (`FieldA.NoFun`) nor δ-reached (`FieldA.TreeField`). -/
def FieldA.kind : FieldA → RecKind
  | .plain _ _ => .plain
  | .drec _ => .directRec
  | .frec _ _ _ _ => .directRec
  | .drecD _ _ => .directRec

/-- the shape the relation reads (`ctorShapesA`, through erasure; R-NoFunRec-1 step 1 (1b)): a
    function-recursive field's is `recursive` at its inner binders' count. -/
def FieldA.shape : FieldA → FieldShape
  | .plain _ _ => .nonrecursive
  | .drec _ => .recursive 0
  | .frec _ _ Bs _ => .recursive (Bs.length + 1)
  | .drecD _ _ => .recursive 0

/-- the field is not function-recursive. -/
def FieldA.NoFun : FieldA → Prop
  | .frec _ _ _ _ => False
  | _ => True

/-- the field is not reached through δ (R-NoDeltaRec-1): its domain is as the family application reads. -/
def FieldA.NoDelta : FieldA → Prop
  | .drecD _ _ => False
  | _ => True

/-- the fields the tree has: plain or directly recursive (R-NoDeltaRec-1). -/
def FieldA.TreeField : FieldA → Prop
  | .frec _ _ _ _ => False
  | .drecD _ _ => False
  | _ => True

theorem FieldA.treeField_of {x : FieldA} (h1 : x.NoFun) (h2 : x.NoDelta) : x.TreeField := by
  cases x <;> first | trivial | exact h1.elim | exact h2.elim

theorem FieldA.noFun_of_treeField {x : FieldA} (h : x.TreeField) : x.NoFun := by
  cases x <;> first | trivial | exact h.elim

theorem FieldA.noDelta_of_treeField {x : FieldA} (h : x.TreeField) : x.NoDelta := by
  cases x <;> first | trivial | exact h.elim

/-- the field at its δ-normal domain (R-NoDeltaRec-3a): a δ-reached field becomes the directly
    recursive field at its indices — its domain's normal form is the family application. Every
    other field is itself. The constructor member's `normA` is its type built from these. -/
def FieldA.norm : FieldA → FieldA
  | .drecD _ idx => .drec idx
  | x => x

theorem FieldA.norm_self {x : FieldA} (h : x.NoDelta) : x.norm = x := by
  cases x <;> first | exact h.elim | rfl

theorem FieldA.map_norm_self {fs : List FieldA} (h : ∀ x ∈ fs, x.NoDelta) :
    fs.map FieldA.norm = fs := by
  induction fs with
  | nil => rfl
  | cons x fs ih =>
      rw [List.map_cons, FieldA.norm_self (h x (List.mem_cons_self _ _)),
        ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem FieldA.norm_shape (x : FieldA) : x.norm.shape = x.shape := by
  cases x <;> rfl

theorem FieldA.norm_kind (x : FieldA) : x.norm.kind = x.kind := by
  cases x <;> rfl

theorem FieldA.norm_noDelta (x : FieldA) : x.norm.NoDelta := by
  cases x <;> trivial

theorem FieldA.norm_noFun (x : FieldA) : x.norm.NoFun ↔ x.NoFun := by
  cases x <;> exact Iff.rfl

theorem FieldA.kind_shape {x : FieldA} (hx : x.NoFun) : x.kind.shape = x.shape := by
  cases x
  · rfl
  · rfl
  · exact hx.elim
  · rfl

theorem FieldA.shape_ne_succ {x : FieldA} (hx : x.NoFun) (j : Nat) : x.shape ≠ .recursive (j + 1) := by
  cases x
  · intro h; cases h
  · intro h; cases h
  · exact hx.elim
  · intro h; cases h

/-- fields that are not function-recursive have no function-recursive shape. -/
theorem FieldA.map_shape_noFun {fs : List FieldA} (hfs : ∀ x ∈ fs, x.NoFun) (ksPre ks : List FieldShape)
    (j : Nat) : fs.map FieldA.shape ≠ ksPre ++ .recursive (j + 1) :: ks := by
  intro h
  have hm : FieldShape.recursive (j + 1) ∈ fs.map FieldA.shape := by rw [h]; simp
  obtain ⟨x, hx, hxs⟩ := List.mem_map.mp hm
  exact FieldA.shape_ne_succ (hfs x hx) j hxs

theorem FieldA.map_kind_shape {fs : List FieldA} (hfs : ∀ x ∈ fs, x.NoFun) :
    (fs.map FieldA.kind).map RecKind.shape = fs.map FieldA.shape := by
  rw [List.map_map]
  exact List.map_congr_left (fun x hx => FieldA.kind_shape (hfs x hx))

/-- the plain field over a domain: a structure's field, or a function-recursive field's inner binder
    read as a plain field. -/
def plainA (d : ExprA × Level) : FieldA := .plain d.1 d.2

theorem plainA_noFun (ds : List (ExprA × Level)) : ∀ x ∈ ds.map plainA, x.NoFun := by
  intro x hx
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
  trivial

theorem plainA_noDelta (ds : List (ExprA × Level)) : ∀ x ∈ ds.map plainA, x.NoDelta := by
  intro x hx
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hx
  trivial

/-- one binder deeper in the current context, with no new plain variable (a recursive
    field). -/
def SubstA.shift1 (σ : SubstA) : SubstA := fun i => liftA 0 1 (σ i)

/-- a function-recursive field's domain, with its sort: the inner binders under the plain
    substitution (each under the earlier ones), then `F ls (pl ++ idx)` at the parameter locals carried
    past them. It is the field telescope at the inner binders read as plain fields (`frecDomA_eq`). -/
def frecDomA (f : Nat) (ls : List Level) (w : Level) :
    List ExprA → SubstA → List (ExprA × Level) → List ExprA → ExprA × Level
  | pl, σ, [], idx => (foldAppsA (.const f ls) (pl ++ idx.map (substA σ)), w)
  | pl, σ, (D, u) :: ds, idx =>
      let r := frecDomA f ls w (pl.map (liftA 0 1)) σ.up ds idx
      (.pi (substA σ D) u r.1 r.2, .imax u r.2)

/-- the fields' telescope and the result `F ls (pl ++ res)`: `pl` are the parameter locals
    at the current depth, `σ` carries the plain context into the current one, `w` is the
    family's sort (each recursive domain's and the result's). A recursive field, directly or
    through inner binders, is dropped from the plain context. -/
def ctorFieldsA (f : Nat) (ls : List Level) (w : Level) :
    List ExprA → SubstA → List FieldA → List ExprA → ExprA × Level
  | pl, σ, [], res => (foldAppsA (.const f ls) (pl ++ res.map (substA σ)), w)
  | pl, σ, .plain D u :: fs, res =>
      let r := ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.up fs res
      (.pi (substA σ D) u r.1 r.2, .imax u r.2)
  | pl, σ, .drec idx :: fs, res =>
      let r := ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res
      (.pi (foldAppsA (.const f ls) (pl ++ idx.map (substA σ))) w r.1 r.2, .imax w r.2)
  | pl, σ, .frec B uB Bs idx :: fs, res =>
      let d := frecDomA f ls w pl σ ((B, uB) :: Bs) idx
      let r := ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res
      (.pi d.1 d.2 r.1 r.2, .imax d.2 r.2)
  | pl, σ, .drecD D _ :: fs, res =>
      let r := ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res
      (.pi (substA σ D) w r.1 r.2, .imax w r.2)

/-- the constructor's stored type, built from its view: the mirrors, then the fields from
    the exact parameter locals and the identity on the plain context. -/
def ctorTypeA (f : Nat) (ls : List Level) (w : Level) (mirrors : List (ExprA × Level))
    (fields : List FieldA) (res : List ExprA) : ExprA :=
  let r := ctorFieldsA f ls w (paramLocalsA mirrors.length) SubstA.id fields res
  (piTelA mirrors r.1 r.2).1

/-- a function-recursive field's sort: its inner binders' over the family's. -/
def frecLevelA (w : Level) : List (ExprA × Level) → Level
  | [] => w
  | (_, u) :: ds => .imax u (frecLevelA w ds)

/-- the fields' telescope's sort: independent of the locals and the substitution. -/
def fieldsLevelA (w : Level) : List FieldA → Level
  | [] => w
  | .plain _ u :: fs => .imax u (fieldsLevelA w fs)
  | .drec _ :: fs => .imax w (fieldsLevelA w fs)
  | .frec B uB Bs _ :: fs => .imax (frecLevelA w ((B, uB) :: Bs)) (fieldsLevelA w fs)
  | .drecD _ _ :: fs => .imax w (fieldsLevelA w fs)

theorem frecDomA_snd (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    (frecDomA f ls w pl σ ds idx).2 = frecLevelA w ds
  | [], _, _ => rfl
  | (_, _) :: ds, pl, σ => by
      simp only [frecDomA, frecLevelA, frecDomA_snd f ls w idx ds]

theorem ctorFieldsA_snd (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    (ctorFieldsA f ls w pl σ fs res).2 = fieldsLevelA w fs
  | [], _, _ => rfl
  | .plain _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, fieldsLevelA, ctorFieldsA_snd f ls w res fs]
  | .drec _ :: fs, pl, σ => by
      simp only [ctorFieldsA, fieldsLevelA, ctorFieldsA_snd f ls w res fs]
  | .frec _ _ _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, fieldsLevelA, ctorFieldsA_snd f ls w res fs, frecDomA_snd]
  | .drecD _ _ :: fs, pl, σ => by
      simp only [ctorFieldsA, fieldsLevelA, ctorFieldsA_snd f ls w res fs]

/-- THE INNER BINDERS ARE PLAIN FIELDS: a function-recursive field's domain is the field telescope at
    its inner binders read as plain fields, ending in the family at its indices. -/
theorem frecDomA_eq (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    frecDomA f ls w pl σ ds idx = ctorFieldsA f ls w pl σ (ds.map plainA) idx
  | [], _, _ => rfl
  | (D, u) :: ds, pl, σ => by
      simp only [frecDomA, List.map, plainA, ctorFieldsA, frecDomA_eq f ls w idx ds]

theorem frecLevelA_eq (w : Level) : (ds : List (ExprA × Level)) →
    frecLevelA w ds = fieldsLevelA w (ds.map plainA)
  | [] => rfl
  | (_, _) :: ds => by simp only [frecLevelA, List.map, plainA, fieldsLevelA, frecLevelA_eq w ds]

/-! ## (2b) the builder's laws

Applying arguments walks the built type as a state machine over `(pl, σ)`: a plain field's
argument extends the plain substitution, a recursive field's is dropped from it, the parameter
locals stay exact; after the parameters `ps` the state is `(ps, consListA ps id)`. -/

/-- arguments consumed left to right as a substitution: the LAST is variable `0`. -/
def consListA : List ExprA → SubstA → SubstA
  | [], τ => τ
  | a :: as, τ => consListA as (SubstA.cons a τ)

/-- the arguments at the plain fields. -/
def plainArgsA : List FieldA → List ExprA → List ExprA
  | .plain _ _ :: fs, a :: as => a :: plainArgsA fs as
  | .drec _ :: fs, _ :: as => plainArgsA fs as
  | .frec _ _ _ _ :: fs, _ :: as => plainArgsA fs as
  | .drecD _ _ :: fs, _ :: as => plainArgsA fs as
  | _, _ => []

theorem consListA_add (as : List ExprA) (τ : SubstA) (k : Nat) :
    consListA as τ (k + as.length) = τ k := by
  induction as generalizing τ k with
  | nil => rfl
  | cons a as ih =>
      show consListA as (SubstA.cons a τ) (k + (as.length + 1)) = τ k
      rw [show k + (as.length + 1) = (k + 1) + as.length by omega, ih]
      rfl

theorem map_substA_id : (pl : List ExprA) → pl.map (substA SubstA.id) = pl
  | [] => rfl
  | p :: pl => by simp only [List.map, substA_id, map_substA_id pl]

theorem map_substA_cons_liftA (a : ExprA) (σ : SubstA) :
    (pl : List ExprA) → (pl.map (liftA 0 1)).map (substA (SubstA.cons a σ)) = pl.map (substA σ)
  | [] => rfl
  | p :: pl => by simp only [List.map, substA_cons_liftA, map_substA_cons_liftA a σ pl]

theorem map_substA_up_liftA (τ : SubstA) :
    (pl : List ExprA) → (pl.map (liftA 0 1)).map (substA τ.up) = (pl.map (substA τ)).map (liftA 0 1)
  | [] => rfl
  | p :: pl => by simp only [List.map, substA_up_liftA, map_substA_up_liftA τ pl]

/-- the parameter locals read the parameters back. -/
theorem paramLocalsA_consListA (ps : List ExprA) (τ : SubstA) :
    (paramLocalsA ps.length).map (substA (consListA ps τ)) = ps := by
  induction ps generalizing τ with
  | nil => rfl
  | cons p ps ih =>
      show substA (consListA ps (SubstA.cons p τ)) (.bvar ps.length) ::
          (paramLocalsA ps.length).map (substA (consListA ps (SubstA.cons p τ))) = p :: ps
      rw [ih, substA_bvar]
      have h := consListA_add ps (SubstA.cons p τ) 0
      rw [Nat.zero_add] at h
      rw [h]
      rfl

theorem instantiate0A_eq_substA_cons (a e : ExprA) :
    instantiate0A a e = substA (SubstA.cons a SubstA.id) e := by
  have h := instantiate0A_substA_up SubstA.id a e
  rw [substA_ext SubstA.id_up e, substA_id] at h
  exact h

theorem substA_foldAppsA (τ : SubstA) :
    (h : ExprA) → (xs : List ExprA) → substA τ (foldAppsA h xs) = foldAppsA (substA τ h) (xs.map (substA τ))
  | _, [] => rfl
  | h, x :: xs => substA_foldAppsA τ (.app h x) xs

theorem piTelA_append (xs ys : List (ExprA × Level)) (B : ExprA) (w : Level) :
    piTelA (xs ++ ys) B w = piTelA xs (piTelA ys B w).1 (piTelA ys B w).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      obtain ⟨D, u⟩ := x
      simp only [List.cons_append, piTelA, List.append_eq, ih]

/-- arguments along a built telescope under a substitution: each extends it. -/
theorem applyTelA_piTelA (B : ExprA) (w : Level) :
    (ms : List (ExprA × Level)) → (ps : List ExprA) → ps.length = ms.length → (τ : SubstA) →
    applyTelA ps (substA τ (piTelA ms B w).1) = some (substA (consListA ps τ) B)
  | [], [], _, _ => rfl
  | (M, u) :: ms, p :: ps, h, τ => by
      simp only [piTelA, substA_pi, applyTelA]
      rw [instantiate0A_substA_up]
      exact applyTelA_piTelA B w ms ps (Nat.succ.inj h) (SubstA.cons p τ)
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

/-- substitution passes through a function-recursive field's domain, as through the field builder. -/
theorem substA_frecDomA (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ τ : SubstA) →
    substA τ (frecDomA f ls w pl σ ds idx).1 =
      (frecDomA f ls w (pl.map (substA τ)) (fun i => substA τ (σ i)) ds idx).1
  | [], pl, σ, τ => by
      simp only [frecDomA, substA_foldAppsA, substA_const, List.map_append, List.map_map]
      congr 3
      exact funext fun e => substA_substA τ σ e
  | (D, u) :: ds, pl, σ, τ => by
      simp only [frecDomA, substA_pi]
      rw [substA_frecDomA f ls w idx ds (pl.map (liftA 0 1)) σ.up τ.up, map_substA_up_liftA,
        substA_substA τ σ D]
      have hσ : (fun i => substA τ.up (σ.up i)) = SubstA.up (fun i => substA τ (σ i)) :=
        funext (substA_substA.comp_up τ σ)
      rw [hσ]
      simp only [frecDomA_snd]

/-- substitution passes through the field builder: on the parameter locals and composed
    onto the plain substitution. -/
theorem substA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ τ : SubstA) →
    substA τ (ctorFieldsA f ls w pl σ fs res).1 =
      (ctorFieldsA f ls w (pl.map (substA τ)) (fun i => substA τ (σ i)) fs res).1
  | [], pl, σ, τ => by
      simp only [ctorFieldsA, substA_foldAppsA, substA_const, List.map_append, List.map_map]
      congr 3
      exact funext fun e => substA_substA τ σ e
  | .plain D u :: fs, pl, σ, τ => by
      simp only [ctorFieldsA, substA_pi]
      rw [substA_ctorFieldsA f ls w res fs (pl.map (liftA 0 1)) σ.up τ.up, map_substA_up_liftA,
        substA_substA τ σ D]
      have hσ : (fun i => substA τ.up (σ.up i)) = SubstA.up (fun i => substA τ (σ i)) :=
        funext (substA_substA.comp_up τ σ)
      rw [hσ]
      simp only [ctorFieldsA_snd]
  | .drec idx :: fs, pl, σ, τ => by
      simp only [ctorFieldsA, substA_pi]
      rw [substA_ctorFieldsA f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up, map_substA_up_liftA,
        substA_foldAppsA, substA_const, List.map_append, List.map_map]
      have hσ : (fun i => substA τ.up (σ.shift1 i)) = SubstA.shift1 (fun i => substA τ (σ i)) :=
        funext fun i => substA_up_liftA τ (σ i)
      have hidx : (substA τ ∘ substA σ) = substA (fun i => substA τ (σ i)) :=
        funext fun e => substA_substA τ σ e
      rw [hσ, hidx]
      simp only [ctorFieldsA_snd]
  | .frec B uB Bs idx :: fs, pl, σ, τ => by
      simp only [ctorFieldsA, substA_pi]
      rw [substA_ctorFieldsA f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up, map_substA_up_liftA,
        substA_frecDomA]
      have hσ : (fun i => substA τ.up (σ.shift1 i)) = SubstA.shift1 (fun i => substA τ (σ i)) :=
        funext fun i => substA_up_liftA τ (σ i)
      rw [hσ]
      simp only [ctorFieldsA_snd, frecDomA_snd]
  | .drecD D idx :: fs, pl, σ, τ => by
      simp only [ctorFieldsA, substA_pi]
      rw [substA_ctorFieldsA f ls w res fs (pl.map (liftA 0 1)) σ.shift1 τ.up, map_substA_up_liftA,
        substA_substA τ σ D]
      have hσ : (fun i => substA τ.up (σ.shift1 i)) = SubstA.shift1 (fun i => substA τ (σ i)) :=
        funext fun i => substA_up_liftA τ (σ i)
      rw [hσ]
      simp only [ctorFieldsA_snd]

/-- a plain field's argument extends the plain substitution. -/
theorem instantiate0A_ctorFieldsA_plain (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (fs : List FieldA) (pl : List ExprA) (σ : SubstA) (a : ExprA) :
    instantiate0A a (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.up fs res).1 =
      (ctorFieldsA f ls w pl (SubstA.cons a σ) fs res).1 := by
  rw [instantiate0A_eq_substA_cons, substA_ctorFieldsA, map_substA_cons_liftA, map_substA_id]
  have hσ : (fun i => substA (SubstA.cons a SubstA.id) (σ.up i)) = SubstA.cons a σ := by
    funext i
    cases i with
    | zero => rfl
    | succ i => simp only [SubstA.up_succ, substA_cons_liftA, substA_id, SubstA.cons_succ]
  rw [hσ]

/-- a recursive field's argument is dropped from the plain substitution. -/
theorem instantiate0A_ctorFieldsA_drec (f : Nat) (ls : List Level) (w : Level) (res : List ExprA)
    (fs : List FieldA) (pl : List ExprA) (σ : SubstA) (a : ExprA) :
    instantiate0A a (ctorFieldsA f ls w (pl.map (liftA 0 1)) σ.shift1 fs res).1 =
      (ctorFieldsA f ls w pl σ fs res).1 := by
  rw [instantiate0A_eq_substA_cons, substA_ctorFieldsA, map_substA_cons_liftA, map_substA_id]
  have hσ : (fun i => substA (SubstA.cons a SubstA.id) (σ.shift1 i)) = σ := by
    funext i
    simp only [SubstA.shift1, substA_cons_liftA, substA_id]
  rw [hσ]

/-- all the fields applied: the result `F ls (pl ++ res)` with the plain arguments
    substituted into the result indices. -/
theorem applyTelA_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (as : List ExprA) → as.length = fs.length → (pl : List ExprA) →
    (σ : SubstA) →
    applyTelA as (ctorFieldsA f ls w pl σ fs res).1 =
      some (foldAppsA (.const f ls) (pl ++ res.map (substA (consListA (plainArgsA fs as) σ))))
  | [], [], _, _, _ => rfl
  | .plain D u :: fs, a :: as, h, pl, σ => by
      simp only [ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_plain]
      exact applyTelA_ctorFieldsA f ls w res fs as (Nat.succ.inj h) pl (SubstA.cons a σ)
  | .drec idx :: fs, a :: as, h, pl, σ => by
      simp only [ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA f ls w res fs as (Nat.succ.inj h) pl σ
  | .frec _ _ _ _ :: fs, a :: as, h, pl, σ => by
      simp only [ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA f ls w res fs as (Nat.succ.inj h) pl σ
  | .drecD _ _ :: fs, a :: as, h, pl, σ => by
      simp only [ctorFieldsA, applyTelA]
      rw [instantiate0A_ctorFieldsA_drec]
      exact applyTelA_ctorFieldsA f ls w res fs as (Nat.succ.inj h) pl σ
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h

/-- THE PARAMETERS APPLIED: the constructor type at parameters `ps` is the field telescope at
    the state `(ps, consListA ps id)` — the parameter locals are exactly `ps`. -/
theorem applyTelA_ctorTypeA_params (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) (ps : List ExprA)
    (hps : ps.length = mirrors.length) :
    applyTelA ps (ctorTypeA f ls w mirrors fields res) =
      some (ctorFieldsA f ls w ps (consListA ps SubstA.id) fields res).1 := by
  have h := applyTelA_piTelA (ctorFieldsA f ls w (paramLocalsA mirrors.length) SubstA.id fields res).1
    (ctorFieldsA f ls w (paramLocalsA mirrors.length) SubstA.id fields res).2 mirrors ps hps SubstA.id
  rw [substA_id] at h
  show applyTelA ps (piTelA mirrors _ _).1 = _
  rw [h, substA_ctorFieldsA, ← hps, paramLocalsA_consListA]
  rfl

/-- parameters, then all the fields: the result `F ls (ps ++ res[plain args])`. -/
theorem applyTelA_ctorTypeA (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) (ps as : List ExprA)
    (hps : ps.length = mirrors.length) (has : as.length = fields.length) :
    applyTelA (ps ++ as) (ctorTypeA f ls w mirrors fields res) =
      some (foldAppsA (.const f ls)
        (ps ++ res.map (substA (consListA (plainArgsA fields as) (consListA ps SubstA.id))))) := by
  rw [applyTelA_append, applyTelA_ctorTypeA_params f ls w mirrors fields res ps hps]
  exact applyTelA_ctorFieldsA f ls w res fields as has ps _

/-! ## (2c) level instantiation passes through the builder -/

theorem instantiateLevelsA_substA (ls : List Level) :
    (e : ExprA) → (σ : SubstA) →
    instantiateLevelsA ls (substA σ e) =
      substA (fun i => instantiateLevelsA ls (σ i)) (instantiateLevelsA ls e)
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, _ => rfl
  | .app f x, σ => by
      simp only [substA, instantiateLevelsA, instantiateLevelsA_substA ls f σ,
        instantiateLevelsA_substA ls x σ]
  | .lam a u b, σ => by
      simp only [substA, instantiateLevelsA, instantiateLevelsA_substA ls a σ,
        instantiateLevelsA_substA ls b σ.up, upLevels ls σ]
  | .pi a u b v, σ => by
      simp only [substA, instantiateLevelsA, instantiateLevelsA_substA ls a σ,
        instantiateLevelsA_substA ls b σ.up, upLevels ls σ]
  | .letE a w b, σ => by
      simp only [substA, instantiateLevelsA, instantiateLevelsA_substA ls a σ,
        instantiateLevelsA_substA ls w σ, instantiateLevelsA_substA ls b σ.up, upLevels ls σ]
  | .lit _, _ => rfl
where
  upLevels (ls : List Level) (σ : SubstA) :
      (fun i => instantiateLevelsA ls (σ.up i)) = SubstA.up (fun i => instantiateLevelsA ls (σ i)) :=
    funext fun i => by
      cases i with
      | zero => rfl
      | succ i => simp only [SubstA.up_succ, instantiateLevelsA_liftA]

/-- a field at instantiated levels. -/
def FieldA.instLevels (ls : List Level) : FieldA → FieldA
  | .plain D u => .plain (instantiateLevelsA ls D) (instLevel ls u)
  | .drec idx => .drec (idx.map (instantiateLevelsA ls))
  | .frec B uB Bs idx => .frec (instantiateLevelsA ls B) (instLevel ls uB) (instDomsA ls Bs)
      (idx.map (instantiateLevelsA ls))
  | .drecD D idx => .drecD (instantiateLevelsA ls D) (idx.map (instantiateLevelsA ls))

theorem FieldA.treeField_instLevels (ls : List Level) {x : FieldA} (hx : x.TreeField) :
    (x.instLevels ls).TreeField := by
  cases x <;> first | trivial | exact hx.elim

theorem FieldA.noFun_instLevels (ls : List Level) {x : FieldA} (hx : x.NoFun) : (x.instLevels ls).NoFun := by
  cases x
  · trivial
  · trivial
  · exact hx.elim
  · trivial



/-- `shape` reads through `norm` — `drecD`'s shape was `.recursive 0` already
    (R-NoDeltaRec-4d-iii). -/
theorem map_shape_norm (fs : List FieldA) :
    (fs.map FieldA.norm).map FieldA.shape = fs.map FieldA.shape := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact FieldA.norm_shape x

/-- `norm` lands every non-function-recursive field inside `TreeField` — `drecD` is a tree
    field on the normed side (R-NoDeltaRec-4d-iii). -/
theorem FieldA.norm_treeField {x : FieldA} (hx : x.NoFun) : x.norm.TreeField := by
  cases x <;> first | trivial | exact hx.elim

/-- `kind` reads through `norm` (R-NoDeltaRec-4d-iii). -/
theorem map_kind_norm (fs : List FieldA) :
    (fs.map FieldA.norm).map FieldA.kind = fs.map FieldA.kind := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  exact FieldA.norm_kind x

/-- `norm` is the identity on `plainA`-built lists (R-NoDeltaRec-4d-iii). -/
theorem map_norm_plainA (ds : List (ExprA × Level)) :
    (ds.map plainA).map FieldA.norm = ds.map plainA := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  rfl

/-- R-NoFunRec-1 step 1 (1c-γ): the shapes read back through level instantiation. -/
theorem map_shape_instLevels (ls : List Level) (fs : List FieldA) :
    (fs.map (FieldA.instLevels ls)).map FieldA.shape = fs.map FieldA.shape := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  cases x
  · rfl
  · rfl
  · simp [Function.comp, FieldA.instLevels, FieldA.shape, instDomsA]
  · rfl

theorem map_kind_instLevels (ls : List Level) (fs : List FieldA) :
    (fs.map (FieldA.instLevels ls)).map FieldA.kind = fs.map FieldA.kind := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  cases x <;> rfl

theorem plainA_instLevels (ls : List Level) (ds : List (ExprA × Level)) :
    (ds.map plainA).map (FieldA.instLevels ls) = (instDomsA ls ds).map plainA := by
  simp only [List.map_map, instDomsA]
  rfl

theorem frecLevelA_instLevel (ls : List Level) (w : Level) : (ds : List (ExprA × Level)) →
    instLevel ls (frecLevelA w ds) = frecLevelA (instLevel ls w) (instDomsA ls ds)
  | [] => rfl
  | (_, _) :: ds => by
      simp only [frecLevelA, instDomsA, List.map, instLevel_imax]
      rw [frecLevelA_instLevel ls w ds]
      rfl

theorem fieldsLevelA_instLevel (ls : List Level) (w : Level) :
    (fs : List FieldA) →
    instLevel ls (fieldsLevelA w fs) = fieldsLevelA (instLevel ls w) (fs.map (FieldA.instLevels ls))
  | [] => rfl
  | .plain _ _ :: fs => by
      simp only [fieldsLevelA, List.map, FieldA.instLevels, instLevel_imax,
        fieldsLevelA_instLevel ls w fs]
  | .drec _ :: fs => by
      simp only [fieldsLevelA, List.map, FieldA.instLevels, instLevel_imax,
        fieldsLevelA_instLevel ls w fs]
  | .drecD _ _ :: fs => by
      simp only [fieldsLevelA, List.map, FieldA.instLevels, instLevel_imax,
        fieldsLevelA_instLevel ls w fs]
  | .frec B uB Bs _ :: fs => by
      have h := frecLevelA_instLevel ls w ((B, uB) :: Bs)
      simp only [fieldsLevelA, List.map, FieldA.instLevels, instLevel_imax,
        fieldsLevelA_instLevel ls w fs, h]
      rfl

theorem map_instantiateLevelsA_liftA (ls : List Level) :
    (pl : List ExprA) →
    (pl.map (liftA 0 1)).map (instantiateLevelsA ls) = (pl.map (instantiateLevelsA ls)).map (liftA 0 1)
  | [] => rfl
  | p :: pl => by
      simp only [List.map, instantiateLevelsA_liftA, map_instantiateLevelsA_liftA ls pl]

theorem instantiateLevelsA_frecDomA (ls : List Level) (f : Nat) (ms : List Level) (w : Level)
    (idx : List ExprA) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) →
    instantiateLevelsA ls (frecDomA f ms w pl σ ds idx).1 =
      (frecDomA f (ms.map (instLevel ls)) (instLevel ls w) (pl.map (instantiateLevelsA ls))
        (fun i => instantiateLevelsA ls (σ i)) (instDomsA ls ds) (idx.map (instantiateLevelsA ls))).1
  | [], pl, σ => by
      simp only [frecDomA, instDomsA, List.map, instantiateLevelsA_foldAppsA, instantiateLevelsA,
        List.map_append, List.map_map]
      congr 3
      exact funext fun e => instantiateLevelsA_substA ls e σ
  | (D, u) :: ds, pl, σ => by
      simp only [frecDomA, instantiateLevelsA, instDomsA, List.map]
      have ih := instantiateLevelsA_frecDomA ls f ms w idx ds (pl.map (liftA 0 1)) σ.up
      simp only [instDomsA] at ih
      rw [ih, map_instantiateLevelsA_liftA, instantiateLevelsA_substA ls D σ,
        instantiateLevelsA_substA.upLevels ls σ, frecDomA_snd, frecDomA_snd]
      have h := frecLevelA_instLevel ls w ds
      simp only [instDomsA] at h
      rw [h]

theorem instantiateLevelsA_ctorFieldsA (ls : List Level) (f : Nat) (ms : List Level) (w : Level)
    (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) →
    instantiateLevelsA ls (ctorFieldsA f ms w pl σ fs res).1 =
      (ctorFieldsA f (ms.map (instLevel ls)) (instLevel ls w) (pl.map (instantiateLevelsA ls))
        (fun i => instantiateLevelsA ls (σ i)) (fs.map (FieldA.instLevels ls))
        (res.map (instantiateLevelsA ls))).1
  | [], pl, σ => by
      simp only [ctorFieldsA, instantiateLevelsA_foldAppsA, instantiateLevelsA, List.map_append,
        List.map_map, List.map]
      congr 3
      exact funext fun e => instantiateLevelsA_substA ls e σ
  | .plain D u :: fs, pl, σ => by
      simp only [ctorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_ctorFieldsA ls f ms w res fs (pl.map (liftA 0 1)) σ.up,
        map_instantiateLevelsA_liftA, instantiateLevelsA_substA ls D σ,
        instantiateLevelsA_substA.upLevels ls σ, ctorFieldsA_snd, ctorFieldsA_snd,
        fieldsLevelA_instLevel]
  | .drec idx :: fs, pl, σ => by
      simp only [ctorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_ctorFieldsA ls f ms w res fs (pl.map (liftA 0 1)) σ.shift1,
        map_instantiateLevelsA_liftA, instantiateLevelsA_foldAppsA, ctorFieldsA_snd,
        ctorFieldsA_snd, fieldsLevelA_instLevel]
      have hσ : (fun i => instantiateLevelsA ls (σ.shift1 i)) =
          SubstA.shift1 (fun i => instantiateLevelsA ls (σ i)) :=
        funext fun i => instantiateLevelsA_liftA ls 0 1 (σ i)
      have hidx : (instantiateLevelsA ls ∘ substA σ) =
          (substA (fun i => instantiateLevelsA ls (σ i)) ∘ instantiateLevelsA ls) :=
        funext fun e => instantiateLevelsA_substA ls e σ
      simp only [instantiateLevelsA, List.map_append, List.map_map, hσ, hidx]
  | .frec B uB Bs idx :: fs, pl, σ => by
      simp only [ctorFieldsA, frecDomA, instantiateLevelsA, List.map, FieldA.instLevels, instDomsA,
        instLevel_imax]
      have hσ : (fun i => instantiateLevelsA ls (σ.shift1 i)) =
          SubstA.shift1 (fun i => instantiateLevelsA ls (σ i)) :=
        funext fun i => instantiateLevelsA_liftA ls 0 1 (σ i)
      have hd := instantiateLevelsA_frecDomA ls f ms w idx Bs (pl.map (liftA 0 1)) σ.up
      simp only [instDomsA] at hd
      rw [instantiateLevelsA_ctorFieldsA ls f ms w res fs (pl.map (liftA 0 1)) σ.shift1, hd,
        map_instantiateLevelsA_liftA, instantiateLevelsA_substA ls B σ,
        instantiateLevelsA_substA.upLevels ls σ, hσ]
      have hl := frecLevelA_instLevel ls w Bs
      simp only [instDomsA] at hl
      simp only [ctorFieldsA_snd, frecDomA_snd, fieldsLevelA_instLevel, hl]
  | .drecD D idx :: fs, pl, σ => by
      simp only [ctorFieldsA, instantiateLevelsA, List.map, FieldA.instLevels]
      rw [instantiateLevelsA_ctorFieldsA ls f ms w res fs (pl.map (liftA 0 1)) σ.shift1,
        map_instantiateLevelsA_liftA, instantiateLevelsA_substA ls D σ, ctorFieldsA_snd,
        ctorFieldsA_snd, fieldsLevelA_instLevel]
      have hσ : (fun i => instantiateLevelsA ls (σ.shift1 i)) =
          SubstA.shift1 (fun i => instantiateLevelsA ls (σ i)) :=
        funext fun i => instantiateLevelsA_liftA ls 0 1 (σ i)
      rw [hσ]

theorem instantiateLevelsA_piTelA (ls : List Level) (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) →
    (instantiateLevelsA ls (piTelA ds B w).1, instLevel ls (piTelA ds B w).2) =
      piTelA (instDomsA ls ds) (instantiateLevelsA ls B) (instLevel ls w)
  | [] => rfl
  | (D, u) :: ds => by
      have ih := instantiateLevelsA_piTelA ls B w ds
      simp only [instDomsA, List.map] at ih ⊢
      simp only [piTelA, instantiateLevelsA, instLevel_imax]
      rw [← ih]

theorem map_instantiateLevelsA_paramLocalsA (ls : List Level) :
    (n : Nat) → (paramLocalsA n).map (instantiateLevelsA ls) = paramLocalsA n
  | 0 => rfl
  | n + 1 => by
      simp only [paramLocalsA, List.map, instantiateLevelsA, map_instantiateLevelsA_paramLocalsA ls n]

/-- level instantiation of a built constructor type is the type built from the instantiated
    view. -/
theorem instantiateLevelsA_ctorTypeA (ls : List Level) (f : Nat) (ms : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) :
    instantiateLevelsA ls (ctorTypeA f ms w mirrors fields res) =
      ctorTypeA f (ms.map (instLevel ls)) (instLevel ls w) (instDomsA ls mirrors)
        (fields.map (FieldA.instLevels ls)) (res.map (instantiateLevelsA ls)) := by
  have h := congrArg Prod.fst (instantiateLevelsA_piTelA ls
    (ctorFieldsA f ms w (paramLocalsA mirrors.length) SubstA.id fields res).1
    (ctorFieldsA f ms w (paramLocalsA mirrors.length) SubstA.id fields res).2 mirrors)
  simp only at h
  show instantiateLevelsA ls (piTelA mirrors _ _).1 = (piTelA (instDomsA ls mirrors) _ _).1
  rw [h, instantiateLevelsA_ctorFieldsA, map_instantiateLevelsA_paramLocalsA, ctorFieldsA_snd,
    ctorFieldsA_snd, fieldsLevelA_instLevel]
  have hlen : (instDomsA ls mirrors).length = mirrors.length := by simp [instDomsA]
  have hid : (fun i => instantiateLevelsA ls (SubstA.id i)) = SubstA.id := funext fun _ => rfl
  rw [hlen, hid]

/-- the canonical universe vector instantiated at a full level list is that list. -/
theorem canonLevelsA_instLevel (ls : List Level) :
    (canonLevelsA ls.length).map (instLevel ls) = ls := by
  apply List.ext_getElem
  · simp [canonLevelsA]
  · intro i h₁ h₂
    simp only [canonLevelsA, List.getElem_map, List.getElem_range, instLevel_param,
      List.getElem?_eq_getElem h₂, Option.getD_some]

/-! ## (2d) the built type's kinds and family, through erasure -/

theorem constsInA_mono {P Q : Nat → Prop} (hPQ : ∀ r, P r → Q r) :
    (e : ExprA) → ConstsInA P e → ConstsInA Q e
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const r _, h => hPQ r h
  | .app f x, ⟨hf, hx⟩ => ⟨constsInA_mono hPQ f hf, constsInA_mono hPQ x hx⟩
  | .lam a _ b, ⟨ha, hb⟩ => ⟨constsInA_mono hPQ a ha, constsInA_mono hPQ b hb⟩
  | .pi a _ b _, ⟨ha, hb⟩ => ⟨constsInA_mono hPQ a ha, constsInA_mono hPQ b hb⟩
  | .letE a w b, ⟨ha, hw, hb⟩ =>
      ⟨constsInA_mono hPQ a ha, constsInA_mono hPQ w hw, constsInA_mono hPQ b hb⟩
  | .lit t, h => by
      cases t with
      | zero => exact hPQ _ h
      | succ n => exact ⟨hPQ _ h.1, hPQ _ h.2⟩

theorem constsInA_liftA {P : Nat → Prop} (k : Nat) :
    (e : ExprA) → (c : Nat) → ConstsInA P e → ConstsInA P (liftA c k e)
  | .bvar i, c, _ => by
      simp only [liftA]
      split <;> trivial
  | .sort _, _, _ => trivial
  | .const _ _, _, h => h
  | .app f x, c, ⟨hf, hx⟩ => ⟨constsInA_liftA k f c hf, constsInA_liftA k x c hx⟩
  | .lam a _ b, c, ⟨ha, hb⟩ => ⟨constsInA_liftA k a c ha, constsInA_liftA k b (c + 1) hb⟩
  | .pi a _ b _, c, ⟨ha, hb⟩ => ⟨constsInA_liftA k a c ha, constsInA_liftA k b (c + 1) hb⟩
  | .letE a w b, c, ⟨ha, hw, hb⟩ =>
      ⟨constsInA_liftA k a c ha, constsInA_liftA k w c hw, constsInA_liftA k b (c + 1) hb⟩
  | .lit _, _, h => h

theorem constsInA_substA {P : Nat → Prop} :
    (e : ExprA) → (σ : SubstA) → ConstsInA P e → (∀ i, ConstsInA P (σ i)) →
    ConstsInA P (substA σ e)
  | .bvar i, _, _, hσ => hσ i
  | .sort _, _, _, _ => trivial
  | .const _ _, _, h, _ => h
  | .app f x, σ, ⟨hf, hx⟩, hσ => ⟨constsInA_substA f σ hf hσ, constsInA_substA x σ hx hσ⟩
  | .lam a _ b, σ, ⟨ha, hb⟩, hσ =>
      ⟨constsInA_substA a σ ha hσ, constsInA_substA b σ.up hb (up σ hσ)⟩
  | .pi a _ b _, σ, ⟨ha, hb⟩, hσ =>
      ⟨constsInA_substA a σ ha hσ, constsInA_substA b σ.up hb (up σ hσ)⟩
  | .letE a w b, σ, ⟨ha, hw, hb⟩, hσ =>
      ⟨constsInA_substA a σ ha hσ, constsInA_substA w σ hw hσ, constsInA_substA b σ.up hb (up σ hσ)⟩
  | .lit _, _, h, _ => h
where
  up (σ : SubstA) (hσ : ∀ i, ConstsInA P (σ i)) : ∀ i, ConstsInA P (σ.up i)
    | 0 => trivial
    | i + 1 => constsInA_liftA 1 (σ i) 0 (hσ i)

theorem constsInA_foldAppsA {P : Nat → Prop} :
    (h : ExprA) → (xs : List ExprA) → ConstsInA P h → (∀ x ∈ xs, ConstsInA P x) →
    ConstsInA P (foldAppsA h xs)
  | _, [], hh, _ => hh
  | h, x :: xs, hh, hxs =>
      constsInA_foldAppsA (.app h x) xs ⟨hh, hxs x (List.mem_cons_self x xs)⟩
        (fun y hy => hxs y (List.mem_cons_of_mem x hy))

/-- the term mentions no `f`. -/
abbrev FreeOfA (f : Nat) (e : ExprA) : Prop := ConstsInA (fun r => r ≠ f) e

theorem occursConst_erase_freeOf {f : Nat} :
    (e : ExprA) → FreeOfA f e → occursConst f (erase e) = false
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const r _, h => by
      show decide (r = f) = false
      exact decide_eq_false h
  | .app a b, ⟨ha, hb⟩ => by
      simp only [erase, occursConst, occursConst_erase_freeOf a ha, occursConst_erase_freeOf b hb,
        Bool.or_false]
  | .lam a _ b, ⟨ha, hb⟩ => by
      simp only [erase, occursConst, occursConst_erase_freeOf a ha, occursConst_erase_freeOf b hb,
        Bool.or_false]
  | .pi a _ b _, ⟨ha, hb⟩ => by
      simp only [erase, occursConst, occursConst_erase_freeOf a ha, occursConst_erase_freeOf b hb,
        Bool.or_false]
  | .letE a w b, ⟨ha, hw, hb⟩ => by
      simp only [erase, occursConst, occursConst_erase_freeOf a ha, occursConst_erase_freeOf w hw,
        occursConst_erase_freeOf b hb, Bool.or_false]
  | .lit t, h => by
      cases t with
      | zero =>
          show decide (f = 1) = false
          exact decide_eq_false (Ne.symm h)
      | succ n =>
          obtain ⟨h1, h2⟩ := h
          show (decide (f = 1) || decide (f = 2)) = false
          rw [decide_eq_false (Ne.symm h1), Bool.false_or]
          exact decide_eq_false (Ne.symm h2)

theorem erase_foldAppsA : (h : ExprA) → (xs : List ExprA) →
    erase (foldAppsA h xs) = foldApps (erase h) (xs.map erase)
  | _, [] => rfl
  | h, x :: xs => erase_foldAppsA (.app h x) xs

theorem appsSpine_foldApps' : (h : Expr Nat) → (ys : List (Expr Nat)) →
    appsSpine (foldApps h ys) = ((appsSpine h).1, (appsSpine h).2 ++ ys)
  | h, [] => by rw [List.append_nil]; rfl
  | h, y :: ys => by
      rw [show foldApps h (y :: ys) = foldApps (.app h y) ys from rfl, appsSpine_foldApps' _ ys]
      simp [appsSpine, List.append_assoc]

/-- a family application mentions the family, through erasure. -/
theorem occursConst_erase_famApp (f : Nat) (ls : List Level) (xs : List ExprA) :
    occursConst f (erase (foldAppsA (.const f ls) xs)) = true := by
  rw [erase_foldAppsA]
  have key : ∀ (h : Expr Nat) (ys : List (Expr Nat)), occursConst f h = true →
      occursConst f (foldApps h ys) = true := by
    intro h ys
    induction ys generalizing h with
    | nil => exact id
    | cons y ys ih => intro hh; exact ih (.app h y) (by simp [occursConst, hh])
  exact key _ _ (by simp [erase, occursConst])

/-- a recursive domain is classified `directRec` through erasure. -/
theorem analyzeField_famApp {f : Nat} {ls : List Level} {xs : List ExprA}
    (hxs : ∀ x ∈ xs, FreeOfA f x) :
    analyzeField f (erase (foldAppsA (.const f ls) xs)) = some RecKind.directRec := by
  have hocc := occursConst_erase_famApp f ls xs
  have hfam : isFamilyApp f (erase (foldAppsA (.const f ls) xs)) = true := by
    rw [erase_foldAppsA]
    simp only [isFamilyApp, appsSpine_foldApps', appsSpine, List.nil_append, erase]
    simp only [decide_True, Bool.true_and, List.all_eq_true, List.mem_map]
    rintro _ ⟨x, hx, rfl⟩
    simp [occursConst_erase_freeOf x (hxs x hx)]
  simp [analyzeField, hocc, hfam]

theorem analyzeField_plain {f : Nat} {D : ExprA} (h : FreeOfA f D) :
    analyzeField f (erase D) = some RecKind.plain := by
  simp [analyzeField, occursConst_erase_freeOf D h]

/-- a field is free of `f`: its domain, or its indices (a δ-reached field's domain names the family
    by construction: its indices only). -/
def FieldA.FreeOf (f : Nat) : FieldA → Prop
  | .plain D _ => FreeOfA f D
  | .drec idx => ∀ a ∈ idx, FreeOfA f a
  | .frec B _ Bs idx => FreeOfA f B ∧ (∀ d ∈ Bs, FreeOfA f d.1) ∧ ∀ a ∈ idx, FreeOfA f a
  | .drecD _ idx => ∀ a ∈ idx, FreeOfA f a

theorem piDomsA_of_not_pi {e : ExprA} (h : ∀ D u C v, e ≠ .pi D u C v) : piDomsA e = [] := by
  cases e with
  | pi D u C v => exact absurd rfl (h D u C v)
  | _ => rfl

theorem piBodyA_of_not_pi {e : ExprA} (h : ∀ D u C v, e ≠ .pi D u C v) : piBodyA e = e := by
  cases e with
  | pi D u C v => exact absurd rfl (h D u C v)
  | _ => rfl

theorem piDomsA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → piDomsA (piTelA ds B w).1 = ds.map Prod.fst ++ piDomsA B
  | [] => rfl
  | (D, u) :: ds => by simp only [piTelA, piDomsA, List.map, List.cons_append, piDomsA_piTelA B w ds]

theorem piBodyA_piTelA (B : ExprA) (w : Level) :
    (ds : List (ExprA × Level)) → piBodyA (piTelA ds B w).1 = piBodyA B
  | [] => rfl
  | (D, u) :: ds => by simp only [piTelA, piBodyA, piBodyA_piTelA B w ds]

/-- the built fields read back their kinds, through erasure (05 §8–12 `AnalyzeField`), when none is
    function-recursive. -/
theorem analyzeFields_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) → (∀ x ∈ fs, x.FreeOf f) →
    (∀ x ∈ fs, x.TreeField) → (∀ p ∈ pl, FreeOfA f p) → (∀ i, FreeOfA f (σ i)) →
    analyzeFields f ((piDomsA (ctorFieldsA f ls w pl σ fs res).1).map erase) =
      some (fs.map FieldA.kind)
  | [], pl, σ, _, _, _, _ => by
      simp only [ctorFieldsA]
      rw [piDomsA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
      rfl
  | .frec _ _ _ _ :: _, _, _, _, hnf, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .drecD _ _ :: _, _, _, _, hnf, _, _ => (hnf _ (List.mem_cons_self _ _)).elim
  | .plain D u :: fs, pl, σ, hfs, hnf, hpl, hσ => by
      simp only [ctorFieldsA, piDomsA, List.map, analyzeFields]
      have hD : FreeOfA f (substA σ D) :=
        constsInA_substA D σ (hfs (.plain D u) (List.mem_cons_self _ _)) hσ
      rw [analyzeField_plain hD, analyzeFields_ctorFieldsA f ls w res fs (pl.map (liftA 0 1)) σ.up
        (fun x hx => hfs x (List.mem_cons_of_mem _ hx)) (fun x hx => hnf x (List.mem_cons_of_mem _ hx))
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA 1 q 0 (hpl q hq))
        (constsInA_substA.up σ hσ)]
      rfl
  | .drec idx :: fs, pl, σ, hfs, hnf, hpl, hσ => by
      simp only [ctorFieldsA, piDomsA, List.map, analyzeFields]
      have hidx : ∀ x ∈ pl ++ idx.map (substA σ), FreeOfA f x := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hpl x hx
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
          exact constsInA_substA a σ (hfs (.drec idx) (List.mem_cons_self _ _) a ha) hσ
      rw [analyzeField_famApp hidx, analyzeFields_ctorFieldsA f ls w res fs (pl.map (liftA 0 1))
        σ.shift1 (fun x hx => hfs x (List.mem_cons_of_mem _ hx)) (fun x hx => hnf x (List.mem_cons_of_mem _ hx))
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA 1 q 0 (hpl q hq))
        (fun i => constsInA_liftA 1 (σ i) 0 (hσ i))]
      rfl

/-- a family application with family-free arguments is `isFamilyApp`, through erasure (read off
    `analyzeField_famApp`, which classifies it `directRec`). -/
theorem isFamilyApp_erase_foldAppsA {f : Nat} {ls : List Level} {xs : List ExprA}
    (hxs : ∀ x ∈ xs, FreeOfA f x) : isFamilyApp f (erase (foldAppsA (.const f ls) xs)) = true := by
  have h := analyzeField_famApp (ls := ls) hxs
  unfold analyzeField at h
  split at h
  · cases h
  · split at h
    · assumption
    · cases h

/-- the erased Π-telescope's domains are the erased domains. -/
theorem piTelE_erase_fst : (e : ExprA) → (piTelE (erase e)).1 = (piDomsA e).map erase
  | .pi A _ B _ => by simp only [erase, piTelE, piDomsA, List.map, piTelE_erase_fst B]
  | .bvar _ => rfl
  | .sort _ => rfl
  | .const _ _ => rfl
  | .app _ _ => rfl
  | .lam _ _ _ => rfl
  | .letE _ _ _ => rfl
  | .lit _ => rfl

/-- an erased Π-telescope mentions `f` when its body does. -/
theorem occursConst_erase_of_body {f : Nat} : (e : ExprA) → occursConst f (erase (piBodyA e)) = true →
    occursConst f (erase e) = true
  | .pi A _ B _, h => by
      simp only [erase, occursConst, occursConst_erase_of_body B h, Bool.or_true]
  | .bvar _, h => h
  | .sort _, h => h
  | .const _ _, h => h
  | .app _ _, h => h
  | .lam _ _ _, h => h
  | .letE _ _ _, h => h
  | .lit _, h => h

/-- a function-recursive field's domain, read through its parts: as many domains as inner binders,
    each free of `f`, and the body the family at arguments free of it. -/
theorem frecDomA_parts (f : Nat) (ls : List Level) (w : Level) (idx : List ExprA)
    (hidx : ∀ a ∈ idx, FreeOfA f a) :
    (ds : List (ExprA × Level)) → (pl : List ExprA) → (σ : SubstA) → (∀ d ∈ ds, FreeOfA f d.1) →
    (∀ p ∈ pl, FreeOfA f p) → (∀ i, FreeOfA f (σ i)) →
    (piDomsA (frecDomA f ls w pl σ ds idx).1).length = ds.length ∧
    (∀ D ∈ piDomsA (frecDomA f ls w pl σ ds idx).1, FreeOfA f D) ∧
    ∃ xs, piBodyA (frecDomA f ls w pl σ ds idx).1 = foldAppsA (.const f ls) xs ∧ ∀ x ∈ xs, FreeOfA f x
  | [], pl, σ, _, hpl, hσ => by
      simp only [frecDomA]
      rw [piDomsA_of_not_pi (foldAppsA_const_ne_pi f ls _),
        piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
      refine ⟨rfl, fun D hD => absurd hD (List.not_mem_nil _), _, rfl, ?_⟩
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpl x hx
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
        exact constsInA_substA a σ (hidx a ha) hσ
  | (D, u) :: ds, pl, σ, hds, hpl, hσ => by
      simp only [frecDomA, piDomsA, piBodyA, List.length_cons]
      obtain ⟨h1, h2, h3⟩ := frecDomA_parts f ls w idx hidx ds (pl.map (liftA 0 1)) σ.up
        (fun d hd => hds d (List.mem_cons_of_mem _ hd))
        (fun p hp => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact constsInA_liftA 1 q 0 (hpl q hq))
        (constsInA_substA.up σ hσ)
      refine ⟨by rw [h1], ?_, h3⟩
      intro D' hD'
      rcases List.mem_cons.mp hD' with rfl | hD'
      · exact constsInA_substA D σ (hds (D, u) (List.mem_cons_self _ _)) hσ
      · exact h2 D' hD'

/-- a family-free domain is read `nonrecursive`. -/
theorem fieldShapeE_plain {f : Nat} {D : ExprA} (h : FreeOfA f D) :
    fieldShapeE f (erase D) = some .nonrecursive := by
  simp [fieldShapeE, occursConst_erase_freeOf D h]

/-- a recursive domain, direct or through inner binders, is read `recursive` at its inner binders'
    count (R-NoFunRec-1 step 1 (1c)). -/
theorem fieldShapeE_frecDomA {f : Nat} {ls : List Level} {w : Level} {idx : List ExprA}
    {ds : List (ExprA × Level)} {pl : List ExprA} {σ : SubstA} (hidx : ∀ a ∈ idx, FreeOfA f a)
    (hds : ∀ d ∈ ds, FreeOfA f d.1) (hpl : ∀ p ∈ pl, FreeOfA f p) (hσ : ∀ i, FreeOfA f (σ i)) :
    fieldShapeE f (erase (frecDomA f ls w pl σ ds idx).1) = some (.recursive ds.length) := by
  obtain ⟨hlen, hfree, xs, hbody, hxs⟩ := frecDomA_parts f ls w idx hidx ds pl σ hds hpl hσ
  have hocc : occursConst f (erase (frecDomA f ls w pl σ ds idx).1) = true := by
    apply occursConst_erase_of_body
    rw [hbody]
    exact occursConst_erase_famApp f ls xs
  have hall : (piTelE (erase (frecDomA f ls w pl σ ds idx).1)).1.all (fun D => !(occursConst f D)) = true := by
    rw [piTelE_erase_fst, List.all_eq_true]
    intro D hD
    obtain ⟨D', hD', rfl⟩ := List.mem_map.mp hD
    rw [occursConst_erase_freeOf D' (hfree D' hD')]
    rfl
  have hfam : isFamilyApp f (piTelE (erase (frecDomA f ls w pl σ ds idx).1)).2 = true := by
    rw [(piTelE_erase _).2, hbody]
    exact isFamilyApp_erase_foldAppsA hxs
  have hl : (piTelE (erase (frecDomA f ls w pl σ ds idx).1)).1.length = ds.length := by
    rw [(piTelE_erase _).1, hlen]
  unfold fieldShapeE
  rw [hocc, hall, hfam, hl]
  rfl

/-- THE SHAPES READ BACK, field by field: the built fields' shapes through erasure (R-NoFunRec-1 step
    1 (1c)), function-recursive ones included. -/
theorem fieldShapesE_ctorFieldsA (f : Nat) (ls : List Level) (w : Level) (res : List ExprA) :
    (fs : List FieldA) → (pl : List ExprA) → (σ : SubstA) → (∀ x ∈ fs, x.FreeOf f) →
    (∀ x ∈ fs, x.NoDelta) → (∀ p ∈ pl, FreeOfA f p) → (∀ i, FreeOfA f (σ i)) →
    fieldShapesE f ((piDomsA (ctorFieldsA f ls w pl σ fs res).1).map erase) =
      some (fs.map FieldA.shape)
  | [], pl, σ, _, _, _, _ => by
      simp only [ctorFieldsA]
      rw [piDomsA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
      rfl
  | x :: fs, pl, σ, hfs, hnd, hpl, hσ => by
      have hpl' : ∀ p ∈ pl.map (liftA 0 1), FreeOfA f p := fun p hp => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact constsInA_liftA 1 q 0 (hpl q hq)
      have hx := hfs x (List.mem_cons_self _ _)
      have hfs' : ∀ y ∈ fs, y.FreeOf f := fun y hy => hfs y (List.mem_cons_of_mem _ hy)
      have hnd' : ∀ y ∈ fs, y.NoDelta := fun y hy => hnd y (List.mem_cons_of_mem _ hy)
      cases x with
      | plain D u =>
          simp only [ctorFieldsA, piDomsA, List.map, fieldShapesE]
          rw [fieldShapeE_plain (constsInA_substA D σ hx hσ),
            fieldShapesE_ctorFieldsA f ls w res fs _ σ.up hfs' hnd' hpl' (constsInA_substA.up σ hσ)]
          rfl
      | drec idx =>
          simp only [ctorFieldsA, piDomsA, List.map, fieldShapesE]
          have h0 := fieldShapeE_frecDomA (f := f) (ls := ls) (w := w) (ds := []) hx
            (fun d hd => absurd hd (List.not_mem_nil _)) hpl hσ
          simp only [frecDomA] at h0
          rw [h0, fieldShapesE_ctorFieldsA f ls w res fs _ σ.shift1 hfs' hnd' hpl'
            (fun i => constsInA_liftA 1 (σ i) 0 (hσ i))]
          rfl
      | frec B uB Bs idx =>
          simp only [ctorFieldsA, piDomsA, List.map, fieldShapesE]
          rw [fieldShapeE_frecDomA hx.2.2
            (fun d hd => by
              rcases List.mem_cons.mp hd with rfl | hd
              · exact hx.1
              · exact hx.2.1 d hd) hpl hσ,
            fieldShapesE_ctorFieldsA f ls w res fs _ σ.shift1 hfs' hnd' hpl'
              (fun i => constsInA_liftA 1 (σ i) 0 (hσ i))]
          rfl
      | drecD D idx => exact (hnd _ (List.mem_cons_self _ _)).elim

theorem paramLocalsA_freeOf (f : Nat) : (n : Nat) → ∀ p ∈ paramLocalsA n, FreeOfA f p
  | 0 => fun _ h => absurd h (List.not_mem_nil _)
  | n + 1 => fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · trivial
      · exact paramLocalsA_freeOf f n p hp

/-- THE KINDS READ BACK: `ctorKindsA` after the mirrors is the fields' kinds, when the fields
    are free of the family. -/
theorem ctorKindsA_ctorTypeA (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA)
    (hfree : ∀ x ∈ fields, x.FreeOf f) (hnf : ∀ x ∈ fields, x.TreeField) :
    ctorKindsA f mirrors.length (ctorTypeA f ls w mirrors fields res) =
      some (fields.map FieldA.kind) := by
  unfold ctorKindsA ctorTypeA
  simp only
  rw [piDomsA_piTelA]
  have hlen : mirrors.length = (mirrors.map Prod.fst).length := by simp
  rw [hlen, List.drop_left]
  exact analyzeFields_ctorFieldsA f ls w res fields _ _ hfree hnf (paramLocalsA_freeOf f _)
    (fun _ => trivial)

/-- THE SHAPES READ BACK: `ctorShapesA` after the mirrors is the fields' shapes, function-recursive
    ones included (R-NoFunRec-1 step 1 (1c)). -/
theorem ctorShapesA_ctorTypeA (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA)
    (hfree : ∀ x ∈ fields, x.FreeOf f) (hnd : ∀ x ∈ fields, x.NoDelta) :
    ctorShapesA f mirrors.length (ctorTypeA f ls w mirrors fields res) =
      some (fields.map FieldA.shape) := by
  unfold ctorShapesA ctorTypeA
  simp only
  rw [piDomsA_piTelA]
  have hlen : mirrors.length = (mirrors.map Prod.fst).length := by simp
  rw [hlen, List.drop_left]
  exact fieldShapesE_ctorFieldsA f ls w res fields _ _ hfree hnd (paramLocalsA_freeOf f _)
    (fun _ => trivial)

/-- THE FAMILY: the built type's result is headed by `f` (`memberFamRefA`). -/
theorem spineHeadRefA_piBodyA_ctorTypeA (f : Nat) (ls : List Level) (w : Level)
    (mirrors : List (ExprA × Level)) (fields : List FieldA) (res : List ExprA) :
    spineHeadRefA (piBodyA (ctorTypeA f ls w mirrors fields res)) = some f := by
  unfold ctorTypeA
  simp only
  rw [piBodyA_piTelA]
  exact go _ _ fields
where
  go : (pl : List ExprA) → (σ : SubstA) → (fs : List FieldA) →
      spineHeadRefA (piBodyA (ctorFieldsA f ls w pl σ fs res).1) = some f
    | pl, σ, [] => by
        simp only [ctorFieldsA]
        rw [piBodyA_of_not_pi (foldAppsA_const_ne_pi f ls _)]
        simp [spineHeadRefA, foldAppsA_const_head]
    | pl, σ, .plain _ _ :: fs => by
        simp only [ctorFieldsA, piBodyA]
        exact go _ _ fs
    | pl, σ, .drec _ :: fs => by
        simp only [ctorFieldsA, piBodyA]
        exact go _ _ fs
    | pl, σ, .frec _ _ _ _ :: fs => by
        simp only [ctorFieldsA, piBodyA]
        exact go _ _ fs
    | pl, σ, .drecD _ _ :: fs => by
        simp only [ctorFieldsA, piBodyA]
        exact go _ _ fs

/-! ## (3) typings: argument lists, mirrors, the fields in the plain context -/

/-- arguments typed along a Π-telescope down to its sort, each instantiating the rest: a FULL
    application (a recursive domain and the result are types). -/
inductive ArgsTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (Γ : LCtxA) :
    ExprA → List ExprA → Type
  | nil (l : Level) : ArgsTyA E I n Γ (.sort l) []
  | cons (A : ExprA) (u : Level) (B : ExprA) (v : Level) (a : ExprA) (as : List ExprA)
      (ha : HasTyA E I n Γ a A) (tl : ArgsTyA E I n Γ (instantiate0A a B) as) :
      ArgsTyA E I n Γ (.pi A u B v) (a :: as)

/-- the parameter mirrors typed-convertible to the family's parameters, position by position,
    in the context of the family's earlier parameters (05 §6.1), their sorts `=ₙ`. -/
inductive MirrorsConvA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    LCtxA → List (ExprA × Level) → List (ExprA × Level) → Type
  | nil (Γ : LCtxA) : MirrorsConvA E I n Γ [] []
  | cons (Γ : LCtxA) (M : ExprA) (um : Level) (P : ExprA) (up : Level)
      (ms ps : List (ExprA × Level)) (hc : TyConvA E I n Γ M P) (hl : eqN um up)
      (tl : MirrorsConvA E I n (.assumption P :: Γ) ms ps) :
      MirrorsConvA E I n Γ ((M, um) :: ms) ((P, up) :: ps)

/-- the fields typed in the PLAIN context: a plain domain at its sort (the context grows by
    it); a recursive field's indices along the family's index telescope `idxTel k` (`k` plain
    fields so far); a function-recursive field's domain as it reads (`frecDomA_eq`): its inner
    binders as plain fields, ending in its indices along the index telescope past them
    (R-NoFunRec-1 step 1 (1c)); then the result indices. -/
inductive FieldsTyA (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) (idxTel : Nat → ExprA) :
    LCtxA → Nat → List FieldA → List ExprA → Type
  | nil (Γ : LCtxA) (k : Nat) (res : List ExprA) (hres : ArgsTyA E I n Γ (idxTel k) res) :
      FieldsTyA E I n idxTel Γ k [] res
  | plain (Γ : LCtxA) (k : Nat) (D : ExprA) (u : Level) (fs : List FieldA) (res : List ExprA)
      (hD : HasTyA E I n Γ D (.sort u))
      (tl : FieldsTyA E I n idxTel (.assumption D :: Γ) (k + 1) fs res) :
      FieldsTyA E I n idxTel Γ k (.plain D u :: fs) res
  | drec (Γ : LCtxA) (k : Nat) (idx : List ExprA) (fs : List FieldA) (res : List ExprA)
      (hidx : ArgsTyA E I n Γ (idxTel k) idx) (tl : FieldsTyA E I n idxTel Γ k fs res) :
      FieldsTyA E I n idxTel Γ k (.drec idx :: fs) res
  | frec (Γ : LCtxA) (k : Nat) (B : ExprA) (uB : Level) (Bs : List (ExprA × Level)) (idx : List ExprA)
      (fs : List FieldA) (res : List ExprA)
      (hdom : FieldsTyA E I n idxTel Γ k (((B, uB) :: Bs).map plainA) idx)
      (tl : FieldsTyA E I n idxTel Γ k fs res) :
      FieldsTyA E I n idxTel Γ k (.frec B uB Bs idx :: fs) res
  | drecD (Γ : LCtxA) (k : Nat) (D : ExprA) (idx : List ExprA) (fs : List FieldA) (res : List ExprA)
      (hidx : ArgsTyA E I n Γ (idxTel k) idx) (tl : FieldsTyA E I n idxTel Γ k fs res) :
      FieldsTyA E I n idxTel Γ k (.drecD D idx :: fs) res

theorem MirrorsConvA.length {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    {Γ : LCtxA} → {ms ps : List (ExprA × Level)} → MirrorsConvA E I n Γ ms ps →
    ms.length = ps.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ _ _ _ _ _ _ _ tl => congrArg Nat.succ tl.length

/-- a term typed in `E` mentions no reference outside `E`; a fresh `f` in particular. -/
theorem freeOfA_of_dom {E : ResolvedEnvA} {f : Nat} (hfresh : E.members f = none) {e : ExprA}
    (h : ConstsInA (domA E) e) : FreeOfA f e :=
  constsInA_mono (fun r hr hrf => by
    obtain ⟨m, hm⟩ := hr
    subst hrf
    rw [hfresh] at hm
    exact Option.noConfusion hm) e h

theorem ArgsTyA.constsIn {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    {T : ExprA} → {as : List ExprA} → ArgsTyA E I n Γ T as → ∀ a ∈ as, ConstsInA (domA E) a
  | _, _, .nil _ => fun _ h => absurd h (List.not_mem_nil _)
  | _, _, .cons _ _ _ _ _ _ ha tl => fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hasTyA_constsIn ha
      · exact tl.constsIn x hx

/-- every argument of a typed application is scope-bounded by its context — the per-argument
    instance of `hasTyA_boundOk` (R-NoDeltaRec-4d: a δ-reached field's `idx` carry their bound
    from the `ArgsTyA` premise `drecD_typed` already supplies). -/
theorem ArgsTyA.boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    {T : ExprA} → {as : List ExprA} → ArgsTyA E I n Γ T as → ∀ a ∈ as, boundOkB Γ.length a = true
  | _, _, .nil _ => fun _ h => absurd h (List.not_mem_nil _)
  | _, _, .cons _ _ _ _ _ _ ha tl => fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hasTyA_boundOk ha
      · exact tl.boundOk x hx

/-- a left-folded `app`-chain's scope bound: the head plus every argument bounded. -/
theorem boundOkB_foldAppsA {c : Nat} (h : ExprA) (as : List ExprA) :
    boundOkB c h = true → (∀ a ∈ as, boundOkB c a = true) →
      boundOkB c (foldAppsA h as) = true := by
  induction as generalizing h with
  | nil => simp only [foldAppsA]; intro hh _; exact hh
  | cons a as ih =>
      simp only [foldAppsA]
      intro hh has
      exact ih _ (andB_true hh (has a (List.mem_cons_self a as)))
        (fun x hx => has x (List.mem_cons_of_mem a hx))

/-- `σ.up`'s range stays bounded one binder deeper for the indices a `c_D`-bound term can
    name: `bvar 0` is in scope, the lifted images are by `boundOkB_liftA` (R-NoDeltaRec-4d). -/
theorem boundOkB_substA_up {σ : SubstA} {c_D c : Nat}
    (hσ : ∀ i, i < c_D → boundOkB c (σ i) = true) :
    ∀ i, i < c_D + 1 → boundOkB (c + 1) (σ.up i) = true
  | 0, _ => decide_eq_true (by omega)
  | i + 1, hi => boundOkB_liftA 0 1 c (σ i) (hσ i (by omega))

/-- the substitution never escapes scope: if `e`'s bvars are under `c_D` and every `σ`-image
    they can name sits under `c`, then `substA σ e` sits under `c` (R-NoDeltaRec-4d). -/
theorem boundOkB_substA :
    ∀ (σ : SubstA) (c_D c : Nat) (e : ExprA),
      (∀ i, i < c_D → boundOkB c (σ i) = true) →
      boundOkB c_D e = true → boundOkB c (substA σ e) = true
  | _, _, _, .bvar i, hσ, h => hσ i (of_decide_eq_true h)
  | _, _, _, .sort _, _, _ => rfl
  | _, _, _, .const _ _, _, _ => rfl
  | σ, c_D, c, .app f x, hσ, h =>
      andB_true (boundOkB_substA σ c_D c f hσ (boolAnd_left h))
        (boundOkB_substA σ c_D c x hσ (boolAnd_right h))
  | σ, c_D, c, .lam a _u b, hσ, h =>
      andB_true (boundOkB_substA σ c_D c a hσ (boolAnd_left h))
        (boundOkB_substA σ.up (c_D + 1) (c + 1) b (boundOkB_substA_up hσ) (boolAnd_right h))
  | σ, c_D, c, .pi a _u b _v, hσ, h =>
      andB_true (boundOkB_substA σ c_D c a hσ (boolAnd_left h))
        (boundOkB_substA σ.up (c_D + 1) (c + 1) b (boundOkB_substA_up hσ) (boolAnd_right h))
  | σ, c_D, c, .letE a w b, hσ, h =>
      andB_true
        (andB_true (boundOkB_substA σ c_D c a hσ (boolAnd_left (boolAnd_left h)))
          (boundOkB_substA σ c_D c w hσ (boolAnd_right (boolAnd_left h))))
        (boundOkB_substA σ.up (c_D + 1) (c + 1) b (boundOkB_substA_up hσ) (boolAnd_right h))
  | _, _, _, .lit _, _, _ => rfl

/-- fields typed in the base are free of a reference fresh in it (05 §6 rule 2: the family
    occurs only as a recursive head and as the result head). -/
theorem FieldsTyA.freeOf {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {idxTel : Nat → ExprA}
    {f : Nat} (hfresh : E.members f = none) :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
    FieldsTyA E I n idxTel Γ k fs res → (∀ x ∈ fs, x.FreeOf f) ∧ ∀ a ∈ res, FreeOfA f a
  | _, _, _, _, .nil _ _ _ hres =>
      ⟨fun _ h => absurd h (List.not_mem_nil _), fun a ha => freeOfA_of_dom hfresh (hres.constsIn a ha)⟩
  | _, _, _, _, .plain _ _ D _ _ _ hD tl =>
      let ih := tl.freeOf hfresh
      ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact freeOfA_of_dom hfresh (hasTyA_constsIn hD)
        · exact ih.1 x hx, ih.2⟩
  | _, _, _, _, .drec _ _ _ _ _ hidx tl =>
      let ih := tl.freeOf hfresh
      ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact fun a ha => freeOfA_of_dom hfresh (hidx.constsIn a ha)
        · exact ih.1 x hx, ih.2⟩
  | _, _, _, _, .frec _ _ _ _ _ _ _ _ hdom tl =>
      let ih := tl.freeOf hfresh
      let ihd := hdom.freeOf hfresh
      ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨ihd.1 _ (List.mem_cons_self _ _),
            fun d hd => ihd.1 (plainA d) (List.mem_cons_of_mem _ (List.mem_map_of_mem _ hd)), ihd.2⟩
        · exact ih.1 x hx, ih.2⟩
  | _, _, _, _, .drecD _ _ _ _ _ _ hidx tl =>
      let ih := tl.freeOf hfresh
      ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact fun a ha => freeOfA_of_dom hfresh (hidx.constsIn a ha)
        · exact ih.1 x hx, ih.2⟩

/-- the plain context after some fields: each plain domain pushed, recursive fields skipped. -/
def plainCtxA : List FieldA → LCtxA → LCtxA
  | [], Γ => Γ
  | .plain D _ :: fs, Γ => plainCtxA fs (.assumption D :: Γ)
  | .drec _ :: fs, Γ => plainCtxA fs Γ
  | .frec _ _ _ _ :: fs, Γ => plainCtxA fs Γ
  | .drecD _ _ :: fs, Γ => plainCtxA fs Γ

/-- the consumed prefix commutes with the tail's context (plain binders stack inward). -/
theorem plainCtxA_append : (xs ys : List FieldA) → (Γ : LCtxA) →
    plainCtxA (xs ++ ys) Γ = plainCtxA ys (plainCtxA xs Γ)
  | [], _, _ => rfl
  | .plain D _u :: xs, ys, Γ => plainCtxA_append xs ys (.assumption D :: Γ)
  | .drec _ :: xs, ys, Γ => plainCtxA_append xs ys Γ
  | .frec _ _ _ _ :: xs, ys, Γ => plainCtxA_append xs ys Γ
  | .drecD _ _ :: xs, ys, Γ => plainCtxA_append xs ys Γ

/-- the plain-field count after some fields, from a start. -/
def plainIdxA : List FieldA → Nat → Nat
  | [], j => j
  | .plain _ _ :: fs, j => plainIdxA fs (j + 1)
  | .drec _ :: fs, j => plainIdxA fs j
  | .frec _ _ _ _ :: fs, j => plainIdxA fs j
  | .drecD _ _ :: fs, j => plainIdxA fs j

/-- `plainIdxA`'s accumulator is a pure offset. -/
theorem plainIdxA_add (fs : List FieldA) : ∀ (j : Nat), plainIdxA fs j = j + plainIdxA fs 0 := by
  induction fs with
  | nil => intro _; rfl
  | cons x fs ih =>
      intro j
      cases x <;> simp only [plainIdxA]
      · rw [ih (j + 1), show plainIdxA fs (0 + 1) = 1 + plainIdxA fs 0 from ih 1]; omega
      · exact ih j
      · exact ih j
      · exact ih j

/-- the instantiated family-parameter telescope's context (R-NoDeltaRec-4d-iii). -/
theorem instCtxA_telCtxA (ls : List Level) (ds : List (ExprA × Level)) :
    instCtxA ls (telCtxA ds) = telCtxA (instDomsA ls ds) := by
  simp only [instCtxA, telCtxA, instDomsA, List.map_reverse, List.map_map]
  rfl

/-- the instantiated plain context is the plain context of the instantiated fields —
    `.drecD` fields skip a binder on both sides (R-NoDeltaRec-4d-iii). -/
theorem instCtxA_plainCtxA (ls : List Level) : (fs : List FieldA) → (Γ : LCtxA) →
    instCtxA ls (plainCtxA fs Γ) = plainCtxA (fs.map (FieldA.instLevels ls)) (instCtxA ls Γ)
  | [], _ => rfl
  | .plain D _ :: fs, Γ => instCtxA_plainCtxA ls fs (.assumption D :: Γ)
  | .drec _ :: fs, Γ => instCtxA_plainCtxA ls fs Γ
  | .frec _ _ _ _ :: fs, Γ => instCtxA_plainCtxA ls fs Γ
  | .drecD _ _ :: fs, Γ => instCtxA_plainCtxA ls fs Γ

/-- `instLevels` keeps the field's constructor, so the plain count is untouched. -/
theorem plainIdxA_instLevels (ls : List Level) : (fs : List FieldA) → (j : Nat) →
    plainIdxA (fs.map (FieldA.instLevels ls)) j = plainIdxA fs j
  | [], _ => rfl
  | .plain _ _ :: fs, j => plainIdxA_instLevels ls fs (j + 1)
  | .drec _ :: fs, j => plainIdxA_instLevels ls fs j
  | .frec _ _ _ _ :: fs, j => plainIdxA_instLevels ls fs j
  | .drecD _ _ :: fs, j => plainIdxA_instLevels ls fs j

/-- `norm` does not change the plain-argument projection (R-NoDeltaRec-4d-iii). -/
theorem plainArgsA_norm : (fs : List FieldA) → (as : List ExprA) →
    plainArgsA (fs.map FieldA.norm) as = plainArgsA fs as
  | [], _ => rfl
  | .plain _ _ :: fs, a :: as => congrArg (a :: ·) (plainArgsA_norm fs as)
  | .drec _ :: fs, _ :: as => plainArgsA_norm fs as
  | .frec _ _ _ _ :: fs, _ :: as => plainArgsA_norm fs as
  | .drecD _ _ :: fs, _ :: as => plainArgsA_norm fs as
  | x :: fs, [] => by cases x <;> rfl

/-- `norm` does not change the plain context (R-NoDeltaRec-4d-iii). -/
theorem plainCtxA_norm : (fs : List FieldA) → (Γ : LCtxA) →
    plainCtxA (fs.map FieldA.norm) Γ = plainCtxA fs Γ
  | [], _ => rfl
  | .plain D _ :: fs, Γ => plainCtxA_norm fs (.assumption D :: Γ)
  | .drec _ :: fs, Γ => plainCtxA_norm fs Γ
  | .frec _ _ _ _ :: fs, Γ => plainCtxA_norm fs Γ
  | .drecD _ _ :: fs, Γ => plainCtxA_norm fs Γ

/-- `norm` does not change the plain-field count (R-NoDeltaRec-4d-iii). -/
theorem plainIdxA_norm : (fs : List FieldA) → (j : Nat) →
    plainIdxA (fs.map FieldA.norm) j = plainIdxA fs j
  | [], _ => rfl
  | .plain _ _ :: fs, j => plainIdxA_norm fs (j + 1)
  | .drec _ :: fs, j => plainIdxA_norm fs j
  | .frec _ _ _ _ :: fs, j => plainIdxA_norm fs j
  | .drecD _ _ :: fs, j => plainIdxA_norm fs j

/-- `plainIdxA` keeps the plain-field count in step with the walked prefix. -/
theorem plainIdxA_append (xs : List FieldA) (ys : List FieldA) (j : Nat) :
    plainIdxA (xs ++ ys) j = plainIdxA ys (plainIdxA xs j) := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih =>
      cases x <;> first | exact ih (j + 1) | exact ih j

/-- `plainCtxA` grows the context by `plainIdxA` exactly. -/
theorem plainCtxA_length (fs : List FieldA) (Γ : LCtxA) :
    (plainCtxA fs Γ).length = Γ.length + plainIdxA fs 0 := by
  induction fs generalizing Γ with
  | nil => rfl
  | cons x fs ih =>
      cases x <;> simp only [plainCtxA, plainIdxA]
      · rw [ih, show plainIdxA fs (0 + 1) = 1 + plainIdxA fs 0 from plainIdxA_add fs 1]
        simp only [List.length_cons]
        omega
      · exact ih _
      · exact ih _
      · exact ih _

/-! ## (4) the views -/

/-- the family view (05 §5): parameters and indices with their sorts and the result sort; the
    stored type is the telescope built from them; the parameter count is the declared one. -/
structure FamViewA (fm : CheckedMemberA) : Type where
  params : List (ExprA × Level)
  indices : List (ExprA × Level)
  sort : Level
  stored : fm.mtypeA = (piTelA (params ++ indices) (.sort sort) (.succ sort)).1
  nparams : params.length = fm.nparamsA
  profile : UniformProp sort ∨ UniformType sort

/-- the family's index telescope, `Π indices, Sort sort`, in the context of its parameters. -/
def FamViewA.idxTelA {fm : CheckedMemberA} (fv : FamViewA fm) : ExprA :=
  (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).1

/-- THE δ-REACHED FIELDS' TYPING (R-NoDeltaRec-2): at each `drecD D idx`, `D` is typed in the family's scope
    (the base extended by the family member) in the plain context before the field, at the family's sort, and
    converts there to `F ls (pl ++ idx)` at the parameter locals past the earlier plain fields. -/
def DrecDTypedA (E : ResolvedEnvA) (I : IotaIfaceA) (f : Nat) (fm : CheckedMemberA) (fv : FamViewA fm)
    (fields : List FieldA) : Prop :=
  ∀ (fsPre : List FieldA) (D : ExprA) (idx : List ExprA) (fsRest : List FieldA),
    fields = fsPre ++ FieldA.drecD D idx :: fsRest →
    Nonempty (HasTyA (extendEnvA E f fm) I fm.arity (plainCtxA fsPre (telCtxA fv.params)) D
      (.sort fv.sort)) ∧
    Nonempty (ConvA (extendEnvA E f fm) I fm.arity (plainCtxA fsPre (telCtxA fv.params)) D
      (foldAppsA (.const f (canonLevelsA fm.arity))
        ((paramLocalsA fv.params.length).map (liftA 0 (plainIdxA fsPre 0)) ++ idx)) (.sort fv.sort)) ∧
    ∀ x ∈ idx, exprLevelsBoundedA fm.arity x = true

theorem drecDTypedA_of_noDelta {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {fields : List FieldA} (h : ∀ x ∈ fields, x.NoDelta) :
    DrecDTypedA E I f fm fv fields := fun fsPre D idx fsRest hfs =>
  (h (.drecD D idx) (by rw [hfs]; exact List.mem_append_right _ (List.mem_cons_self _ _))).elim

/-- membership gives a split (the tree side's `List.mem_split'`; `RcicAnnGroup` is upstream of it). -/
private theorem fieldAMem_split {x : FieldA} {l : List FieldA} (h : x ∈ l) :
    ∃ s t, l = s ++ x :: t := by
  induction l with
  | nil => exact absurd h (List.not_mem_nil _)
  | cons y ys ih =>
      cases h with
      | head => exact ⟨[], ys, rfl⟩
      | tail _ h' => obtain ⟨s, t, rfl⟩ := ih h'; exact ⟨y :: s, t, rfl⟩

/-- the per-member bound — a `drecD` field's `∀ idx` side is evidence, read off the view
    (R-NoDeltaRec-4d-i; the tree side's `drecDTypedT_idxBounded`). -/
theorem drecDTypedA_idxBounded {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} {fields : List FieldA} (hdd : DrecDTypedA E I f fm fv fields)
    {D : ExprA} {idx : List ExprA} (hmem : FieldA.drecD D idx ∈ fields) :
    ∀ x ∈ idx, exprLevelsBoundedA fm.arity x = true := by
  obtain ⟨fsPre, fsRest, rfl⟩ := fieldAMem_split hmem
  exact (hdd fsPre D idx fsRest rfl).2.2

/-! ### scope bounds for the built constructor type (R-NoDeltaRec-4d-ii)

`ctorTypeA`'s Π-chain is scope-bounded (`boundOkB 0`) once its pieces are: the mirrors carry
their bound from the parameters they convert, the fields from `FieldsTyA` (+ `DrecDTypedA` for
`drecD`'s surface domain), the locals and the substitution from the recursion's invariants. This
is what the `hclT`/`stored`-consumers need once `map_norm_self` no longer applies. -/

/-- the arithmetic shuffle the Π-chain proofs need: `(c + 1) + j = c + (j + 1)`. -/
private theorem ctxLen_succ_add (c j : Nat) : c + 1 + j = c + (j + 1) := by omega

/-- boundOk propagates across `TyConvA` in both directions: `of` carries the endpoint typings,
    `refl` is syntactic identity, `trans` chains (the `refl` arm is why the bound is pulled
    through the conversion instead of proved off `TyConvA` alone). -/
theorem tyConvA_boundOk_left {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    ∀ {A B : ExprA}, TyConvA E I n Γ A B → boundOkB Γ.length B = true →
      boundOkB Γ.length A = true
  | _, _, .refl _ _ => id
  | _, _, .of _ _ _ _ _ _ hA _ _ _ _ => fun _ => hasTyA_boundOk hA
  | _, _, .trans _ _ _ _ h1 h2 => fun hB => tyConvA_boundOk_left h1 (tyConvA_boundOk_left h2 hB)

/-- the rightward direction of the same propagation. -/
theorem tyConvA_boundOk_right {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {Γ : LCtxA} :
    ∀ {A B : ExprA}, TyConvA E I n Γ A B → boundOkB Γ.length A = true →
      boundOkB Γ.length B = true
  | _, _, .refl _ _ => id
  | _, _, .of _ _ _ _ _ _ _ _ hB _ _ => fun _ => hasTyA_boundOk hB
  | _, _, .trans _ _ _ _ h1 h2 => fun hA => tyConvA_boundOk_right h2 (tyConvA_boundOk_right h1 hA)

/-- a `piTelA` chain is scope-bounded from the front: each domain under the earlier binders, the
    body under all of them. -/
theorem piTelA_boundOk :
    ∀ (ds : List (ExprA × Level)) (B : ExprA) (w : Level) (base : Nat),
      (∀ j (D : ExprA) (u : Level), ds.get? j = some (D, u) → boundOkB (base + j) D = true) →
      boundOkB (base + ds.length) B = true → boundOkB base (piTelA ds B w).1 = true
  | [], B, _, _, _, hB => hB
  | (D, u) :: ds, B, w, base, hds, hB => by
      simp only [piTelA]
      exact andB_true (by simpa using hds 0 D u rfl)
        (piTelA_boundOk ds B w (base + 1)
          (fun j D' u' hj => by
            have h := hds (j + 1) D' u' (by simpa using hj)
            rwa [← ctxLen_succ_add] at h)
          (by
            have h := hB
            rwa [List.length_cons, ← ctxLen_succ_add] at h))

/-- the reverse: a bounded `piTelA` bounds each domain at its depth and the body past them. -/
theorem piTelA_boundOk_rev :
    ∀ (ds : List (ExprA × Level)) (B : ExprA) (w : Level) (base : Nat),
      boundOkB base (piTelA ds B w).1 = true →
      (∀ j (D : ExprA) (u : Level), ds.get? j = some (D, u) → boundOkB (base + j) D = true) ∧
      boundOkB (base + ds.length) B = true
  | [], _, _, base, h => ⟨fun _ _ _ h' => absurd h' Option.noConfusion, h⟩
  | (D, u) :: ds, B, w, base, h => by
      simp only [piTelA] at h
      obtain ⟨ih1, ih2⟩ := piTelA_boundOk_rev ds B w (base + 1) (boolAnd_right h)
      refine ⟨fun j D' u' hj => ?_, ?_⟩
      · cases j with
        | zero =>
            simp only [List.get?_cons_zero] at hj
            obtain ⟨rfl, rfl⟩ := (Prod.mk.injEq ..).mp (Option.some.inj hj)
            exact boolAnd_left h
        | succ j =>
            simp only [List.get?_cons_succ] at hj
            have h' := ih1 j D' u' hj
            rwa [show base + 1 + j = base + (j + 1) from by omega] at h'
      · have h' := ih2
        rwa [List.length_cons,
          show base + (ds.length + 1) = base + 1 + ds.length from by omega]

/-- `paramLocalsA n`'s entries are `bvar`s below `n`. -/
theorem paramLocalsA_boundOkB : (n : Nat) → (c : Nat) → n ≤ c →
    ∀ x ∈ paramLocalsA n, boundOkB c x = true
  | 0, _, _ => fun x hx => absurd hx (List.not_mem_nil _)
  | n + 1, c, hnc => fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hx
      · exact decide_eq_true (by omega)
      · exact paramLocalsA_boundOkB n c (by omega) x hx

/-- `substA`'s `shift1` image stays bounded one binder deeper. -/
theorem boundOkB_substA_shift1 {σ : SubstA} {c_D c : Nat}
    (hσ : ∀ i, i < c_D → boundOkB c (σ i) = true) :
    ∀ i, i < c_D → boundOkB (c + 1) (σ.shift1 i) = true := fun i hi =>
  boundOkB_liftA 0 1 c (σ i) (hσ i hi)

/-- `liftA`-mapped locals stay bounded one binder deeper. -/
theorem boundOkB_map_liftA {pl : List ExprA} {c : Nat}
    (h : ∀ x ∈ pl, boundOkB c x = true) :
    ∀ x ∈ pl.map (liftA 0 1), boundOkB (c + 1) x = true := fun x hx => by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact boundOkB_liftA 0 1 c y (h y hy)

/-- each mirror domain is bounded at its position: `TyConvA` gives the conversion, the family's
    parameter domains carry the bound (the `refl` arm's missing typing is bridged this way). -/
theorem mirrorsConvA_boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} :
    ∀ {Γ : LCtxA} {ms ps : List (ExprA × Level)},
      MirrorsConvA E I n Γ ms ps →
      (∀ j (P : ExprA) (u : Level), ps.get? j = some (P, u) → boundOkB (Γ.length + j) P = true) →
      ∀ j (M : ExprA) (u : Level), ms.get? j = some (M, u) → boundOkB (Γ.length + j) M = true
  | _, _, _, .nil _, _ => fun _ _ _ h => absurd h Option.noConfusion
  | _, _, _, .cons Γ M um P up ms ps hc hl tl, hps => fun j M' u' hj => by
      cases j with
      | zero =>
          simp only [List.get?_cons_zero] at hj
          obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp (Option.some.inj hj)
          exact tyConvA_boundOk_left hc (hps 0 P up rfl)
      | succ j =>
          simp only [List.get?_cons_succ] at hj
          have htl := mirrorsConvA_boundOk tl
            (fun j' P' u'' hP' => by
              have h := hps (j' + 1) P' u'' (by simpa using hP')
              rwa [← ctxLen_succ_add] at h) j M' u' hj
          rwa [show Γ.length + (j + 1) = (LocalDeclA.assumption P :: Γ).length + j from by
            simp only [List.length_cons]; omega]

/-- a `FieldsTyA` over `plainA`-mapped inner binders bounds each domain at its plain depth and
    the result args past them (the `frec` inner binders read as plain fields). -/
theorem fieldsTyA_mapPlain_boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} :
    ∀ (ds : List (ExprA × Level)) (Γ : LCtxA) (k : Nat) (res : List ExprA),
      FieldsTyA E I n idxTel Γ k (ds.map plainA) res →
      (∀ j (D : ExprA) (u : Level), ds.get? j = some (D, u) → boundOkB (Γ.length + j) D = true) ∧
      (∀ x ∈ res, boundOkB (Γ.length + ds.length) x = true)
  | [], Γ, k, res, .nil _ _ _ hres =>
      ⟨fun _ _ _ h => absurd h Option.noConfusion,
       fun x hx => hres.boundOk x hx⟩
  | (D, u) :: ds, Γ, k, res, .plain _ _ _ _ _ _ hD tl => by
      obtain ⟨ih1, ih2⟩ := fieldsTyA_mapPlain_boundOk ds (.assumption D :: Γ) (k + 1) res tl
      refine ⟨fun j D' u' hj => ?_, fun x hx => ?_⟩
      · cases j with
        | zero =>
            simp only [List.get?_cons_zero] at hj
            cases hj
            exact hasTyA_boundOk hD
        | succ j =>
            simp only [List.get?_cons_succ] at hj
            have h := ih1 j D' u' hj
            rwa [List.length_cons, ctxLen_succ_add] at h
      · have h := ih2 x hx
        rwa [List.length_cons, ctxLen_succ_add] at h

/-- the `frec` domain's inner Π-chain is bounded when the inner binders' domains, the indices,
    the carried locals, and the substitution's range are (R-NoDeltaRec-4d). -/
theorem frecDomA_boundOk (f : Nat) (ls : List Level) (w : Level) :
    ∀ (ds : List (ExprA × Level)) (idx pl : List ExprA) (σ : SubstA) (c cD : Nat),
      (∀ j (D : ExprA) (u : Level), ds.get? j = some (D, u) → boundOkB (cD + j) D = true) →
      (∀ x ∈ idx, boundOkB (cD + ds.length) x = true) →
      (∀ x ∈ pl, boundOkB c x = true) →
      (∀ i, i < cD → boundOkB c (σ i) = true) →
      boundOkB c (frecDomA f ls w pl σ ds idx).1 = true
  | [], idx, pl, σ, c, cD, _, hidx, hpl, hσ => by
      simp only [frecDomA]
      exact boundOkB_foldAppsA _ _ rfl fun x hx => by
        rcases List.mem_append.mp hx with hp | hi
        · exact hpl x hp
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hi
          exact boundOkB_substA σ cD c y hσ (hidx y hy)
  | (D, u) :: ds, idx, pl, σ, c, cD, hds, hidx, hpl, hσ => by
      simp only [frecDomA]
      refine andB_true (boundOkB_substA σ cD c D hσ (by simpa using hds 0 D u rfl)) ?_
      exact frecDomA_boundOk f ls w ds idx (pl.map (liftA 0 1)) σ.up (c + 1) (cD + 1)
        (fun j D' u' hj => by
          have h := hds (j + 1) D' u' (by simpa using hj)
          rwa [← ctxLen_succ_add] at h)
        (fun x hx => by
          have h := hidx x hx
          rwa [List.length_cons, ← ctxLen_succ_add] at h)
        (boundOkB_map_liftA hpl) (boundOkB_substA_up hσ)

/-- the built fields' telescope stays in scope at the ambient cutoff (R-NoDeltaRec-4d): `pl`
    bounded at `c`, σ's images bounded where the source context can name them, each field's
    evidence from `FieldsTyA`, and `drecD`'s surface domain from `DrecDTypedA`. -/
theorem ctorFieldsA_boundOk {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} {f : Nat} {ls : List Level} {w : Level}
    {fm : CheckedMemberA} {fv : FamViewA fm} :
    ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I n idxTel Γ k fs res →
      ∀ (fsPre : List FieldA), Γ = plainCtxA fsPre (telCtxA fv.params) →
        DrecDTypedA E I f fm fv (fsPre ++ fs) →
      ∀ (pl : List ExprA) (σ : SubstA) (c : Nat),
        (∀ x ∈ pl, boundOkB c x = true) →
        (∀ i, i < Γ.length → boundOkB c (σ i) = true) →
      boundOkB c (ctorFieldsA f ls w pl σ fs res).1 = true
  | Γ, k, [], res, .nil _ _ _ hres, fsPre, hΓ, _, pl, σ, c, hpl, hσ => by
      simp only [ctorFieldsA]
      exact boundOkB_foldAppsA _ _ rfl fun x hx => by
        rcases List.mem_append.mp hx with hp | hr
        · exact hpl x hp
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
          exact boundOkB_substA σ Γ.length c y hσ (hres.boundOk y hy)
  | Γ, k, .plain D u :: fs, res, .plain _ _ _ _ _ _ hD tl, fsPre, hΓ, hdd, pl, σ, c, hpl, hσ => by
      simp only [ctorFieldsA]
      refine andB_true (boundOkB_substA σ Γ.length c D hσ (hasTyA_boundOk hD)) ?_
      have hΓ' : .assumption D :: Γ = plainCtxA (fsPre ++ [.plain D u]) (telCtxA fv.params) := by
        rw [plainCtxA_append]; rw [hΓ]; rfl
      exact ctorFieldsA_boundOk tl (fsPre ++ [.plain D u]) hΓ' (by
        rw [List.append_assoc]; exact hdd) (pl.map (liftA 0 1)) σ.up (c + 1)
        (boundOkB_map_liftA hpl) (by
          intro i hi
          simp only [List.length_cons] at hi
          exact boundOkB_substA_up hσ i hi)
  | Γ, k, .drec idx :: fs, res, .drec _ _ _ _ _ hidx tl, fsPre, hΓ, hdd, pl, σ, c, hpl, hσ => by
      simp only [ctorFieldsA]
      refine andB_true ?_ ?_
      · exact boundOkB_foldAppsA _ _ rfl fun x hx => by
          rcases List.mem_append.mp hx with hp | hi
          · exact hpl x hp
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hi
            exact boundOkB_substA σ Γ.length c y hσ (hidx.boundOk y hy)
      · have hΓ' : Γ = plainCtxA (fsPre ++ [.drec idx]) (telCtxA fv.params) := by
          rw [plainCtxA_append]; exact hΓ
        exact ctorFieldsA_boundOk tl (fsPre ++ [.drec idx]) hΓ' (by
          rw [List.append_assoc]; exact hdd) (pl.map (liftA 0 1)) σ.shift1 (c + 1)
          (boundOkB_map_liftA hpl) (boundOkB_substA_shift1 hσ)
  | Γ, k, .frec B uB Bs idx :: fs, res, .frec _ _ _ _ _ _ _ _ hdom tl, fsPre, hΓ, hdd, pl, σ,
      c, hpl, hσ => by
      simp only [ctorFieldsA]
      obtain ⟨hds, hidx'⟩ := fieldsTyA_mapPlain_boundOk ((B, uB) :: Bs) Γ k idx hdom
      refine andB_true ?_ ?_
      · exact frecDomA_boundOk f ls w ((B, uB) :: Bs) idx pl σ c Γ.length hds hidx' hpl hσ
      · have hΓ' : Γ = plainCtxA (fsPre ++ [.frec B uB Bs idx]) (telCtxA fv.params) := by
          rw [plainCtxA_append]; exact hΓ
        exact ctorFieldsA_boundOk tl (fsPre ++ [.frec B uB Bs idx]) hΓ' (by
          rw [List.append_assoc]; exact hdd) (pl.map (liftA 0 1)) σ.shift1 (c + 1)
          (boundOkB_map_liftA hpl) (boundOkB_substA_shift1 hσ)
  | Γ, k, .drecD D idx :: fs, res, .drecD _ _ _ _ _ _ hidx tl, fsPre, hΓ, hdd, pl, σ, c, hpl,
      hσ => by
      simp only [ctorFieldsA]
      refine andB_true ?_ ?_
      · obtain ⟨hD', _⟩ := hdd fsPre D idx fs rfl
        obtain ⟨hD''⟩ := hD'
        have hL : (plainCtxA fsPre (telCtxA fv.params)).length = Γ.length := by rw [← hΓ]
        exact boundOkB_substA σ Γ.length c D hσ (hL ▸ hasTyA_boundOk hD'')
      · have hΓ' : Γ = plainCtxA (fsPre ++ [.drecD D idx]) (telCtxA fv.params) := by
          rw [plainCtxA_append]; exact hΓ
        exact ctorFieldsA_boundOk tl (fsPre ++ [.drecD D idx]) hΓ' (by
          rw [List.append_assoc]; exact hdd) (pl.map (liftA 0 1)) σ.shift1 (c + 1)
          (boundOkB_map_liftA hpl) (boundOkB_substA_shift1 hσ)

/-- `FieldsTyA` survives `FieldA.norm`: a `drecD` field maps to `drec`, and its premise
    `ArgsTyA` is exactly the one `drec`'s constructor asks for (R-NoDeltaRec-4d). -/
def FieldsTyA.norm {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {idxTel : Nat → ExprA} :
    ∀ {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA},
      FieldsTyA E I n idxTel Γ k fs res → FieldsTyA E I n idxTel Γ k (fs.map FieldA.norm) res
  | _, _, _, _, .nil Γ k res hres => .nil Γ k res hres
  | _, _, _, _, .plain Γ k D u fs res hD tl => .plain Γ k D u _ res hD tl.norm
  | _, _, _, _, .drec Γ k idx fs res hidx tl => .drec Γ k idx _ res hidx tl.norm
  | _, _, _, _, .frec Γ k B uB Bs idx fs res hdom tl => .frec Γ k B uB Bs idx _ res hdom tl.norm
  | _, _, _, _, .drecD Γ k D idx fs res hidx tl => .drec Γ k idx _ res hidx tl.norm

/-- the constructor view (05 §6–§8), in the base scope `E`: the parameter mirrors, the fields
    and the result indices in the plain context, the stored type built from them. -/
structure CtorViewA (E : ResolvedEnvA) (I : IotaIfaceA) (f : Nat) (fm : CheckedMemberA)
    (fv : FamViewA fm) (cm : CheckedMemberA) : Type where
  mirrors : List (ExprA × Level)
  fields : List FieldA
  res : List ExprA
  stored : cm.mtypeA = ctorTypeA f (canonLevelsA fm.arity) fv.sort mirrors fields res
  mirrorsConv : MirrorsConvA E I fm.arity [] mirrors fv.params
  typed : FieldsTyA E I fm.arity (fun k => liftA 0 k fv.idxTelA) (telCtxA fv.params) 0 fields res
  univ : ∀ D u, FieldA.plain D u ∈ fields → UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN u fv.sort)
  /-- a function-recursive field's inner domains are bounded as a plain field's are (05 §7). -/
  univI : ∀ B uB Bs idx, FieldA.frec B uB Bs idx ∈ fields → ∀ d ∈ (B, uB) :: Bs,
    UniformProp fv.sort ∨ (UniformType fv.sort ∧ leN d.2 fv.sort)
  /-- a δ-reached field's domain is typed in the family scope, in the plain context before it, at the
      family's sort, and converts to the family application at the field's indices (R-NoDeltaRec-2). -/
  drecD_typed : DrecDTypedA E I f fm fv fields
  /-- the stored type CONVERTS to its δ-normal form in the family's extension scope
      (R-NoDeltaRec-4d-iii): the mirrors' telescope is shared and each `.drecD` domain converts to
      the family application at its indices — the witness is assembled at the bridge, where the
      sort-uniqueness data for the params↔mirrors substitution lives. -/
  normConv : Nonempty (TyConvA (extendEnvA E f fm) I fm.arity []
    (ctorTypeA f (canonLevelsA fm.arity) fv.sort mirrors fields res)
    (ctorTypeA f (canonLevelsA fm.arity) fv.sort mirrors (fields.map FieldA.norm) res))
  /-- the δ-normal type's own typing in the family's extension scope — `normConv` does not carry
      it on `refl`. -/
  normTyped : ∃ l', Nonempty (HasTyA (extendEnvA E f fm) I fm.arity []
    (ctorTypeA f (canonLevelsA fm.arity) fv.sort mirrors (fields.map FieldA.norm) res) (.sort l'))

section ViewLaws
variable {E : ResolvedEnvA} {I : IotaIfaceA} {f : Nat} {fm cm : CheckedMemberA}

theorem isArity_erase_piTelA (s : Level) (w : Level) :
    (ds : List (ExprA × Level)) → isArity (erase (piTelA ds (.sort s) w).1) = true
  | [] => rfl
  | (D, u) :: ds => by simp only [piTelA, erase, isArity, isArity_erase_piTelA s w ds]

/-- the family's stored type is an arity (00 §19.2 erratum 3), by construction. -/
theorem FamViewA.isArity (fv : FamViewA fm) : isArity (erase fm.mtypeA) = true := by
  rw [fv.stored]; exact isArity_erase_piTelA _ _ _

/-- `telCtxA`'s length is the telescope's. -/
theorem telCtxA_length (ds : List (ExprA × Level)) : (telCtxA ds).length = ds.length := by
  simp only [telCtxA, List.length_reverse, List.length_map]

/-- the built constructor type is closed: scope-bounded at `[]` (R-NoDeltaRec-4d-ii). The
    parameter domains' bound comes in from the caller — `fm.mtypeA`'s own typing decomposes
    to it (`piTelA_boundOk_rev` on `fv.stored`); this is what the `hclT` sites rewrite to once
    `map_norm_self` no longer collapses the δ-reached fields. -/
theorem ctorTypeA_boundOk {fv : FamViewA fm} (view : CtorViewA E I f fm fv cm)
    (hparams : ∀ j (P : ExprA) (u : Level), fv.params.get? j = some (P, u) →
      boundOkB j P = true) :
    boundOkB 0 (ctorTypeA f (canonLevelsA fm.arity) fv.sort view.mirrors view.fields
      view.res) = true := by
  simp only [ctorTypeA]
  apply piTelA_boundOk
  · exact mirrorsConvA_boundOk view.mirrorsConv (by
      intro j P u hP
      simpa using hparams j P u hP)
  · have hlen : (telCtxA fv.params).length = view.mirrors.length := by
      rw [telCtxA_length, view.mirrorsConv.length]
    simp only [Nat.zero_add]
    exact ctorFieldsA_boundOk (ls := canonLevelsA fm.arity) (w := fv.sort) view.typed [] rfl
      view.drecD_typed (paramLocalsA view.mirrors.length) SubstA.id view.mirrors.length
      (paramLocalsA_boundOkB _ _ (Nat.le_refl _)) (fun i hi => by
        rw [hlen] at hi
        simp only [SubstA.id_apply]
        exact decide_eq_true hi)

/-- the δ-normal constructor type is closed too — the normed fields' `drec` arms carry the same
    `ArgsTyA` indices, and `drecD` is gone (R-NoDeltaRec-4d-ii). -/
theorem ctorTypeA_norm_boundOk {fv : FamViewA fm} (view : CtorViewA E I f fm fv cm)
    (hparams : ∀ j (P : ExprA) (u : Level), fv.params.get? j = some (P, u) →
      boundOkB j P = true) :
    boundOkB 0 (ctorTypeA f (canonLevelsA fm.arity) fv.sort view.mirrors
      (view.fields.map FieldA.norm) view.res) = true := by
  simp only [ctorTypeA]
  apply piTelA_boundOk
  · exact mirrorsConvA_boundOk view.mirrorsConv (by
      intro j P u hP
      simpa using hparams j P u hP)
  · simp only [Nat.zero_add]
    exact ctorFieldsA_boundOk (ls := canonLevelsA fm.arity) (w := fv.sort) view.typed.norm
      [] rfl (drecDTypedA_of_noDelta (fun x hx => by
        obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
        exact y.norm_noDelta))
      (paramLocalsA view.mirrors.length) SubstA.id view.mirrors.length
      (paramLocalsA_boundOkB _ _ (Nat.le_refl _)) (fun i hi => by
        have hlen : (telCtxA fv.params).length = view.mirrors.length := by
          rw [telCtxA_length, view.mirrorsConv.length]
        rw [hlen] at hi
        simp only [SubstA.id_apply]
        exact decide_eq_true hi)

/-- the stored constructor type instantiated at `ls` is the constructor type over the
    instantiated (raw) fields — `stored` + `instantiateLevelsA_ctorTypeA` (R-NoDeltaRec-4d-iii:
    the former view field, rebuilt as a lemma off `stored`). -/
theorem CtorViewA.inst_tel (view : CtorViewA E I f fm fv cm) (ls : List Level)
    (hls : ls.length = fm.arity) :
    instantiateLevelsA ls cm.mtypeA =
      ctorTypeA f ls (instLevel ls fv.sort) (instDomsA ls view.mirrors)
        (view.fields.map (FieldA.instLevels ls))
        (view.res.map (instantiateLevelsA ls)) := by
  rw [view.stored, instantiateLevelsA_ctorTypeA,
    show (canonLevelsA fm.arity).map (instLevel ls) = ls from by
      rw [← hls]; exact canonLevelsA_instLevel ls]

theorem FamViewA.piBody (fv : FamViewA fm) : piBodyA fm.mtypeA = .sort fv.sort := by
  rw [fv.stored, piBodyA_piTelA]; rfl

/-- THE FAMILY AT ITS PARAMETERS: the instantiated family type applied to `nparamsA`
    arguments is the instantiated index telescope with the parameters substituted. -/
theorem FamViewA.applyTel_params (fv : FamViewA fm) (ls : List Level) (ps : List ExprA)
    (hps : ps.length = fm.nparamsA) :
    applyTelA ps (instantiateLevelsA ls fm.mtypeA) =
      some (substA (consListA ps SubstA.id) (instantiateLevelsA ls fv.idxTelA)) := by
  have h := congrArg Prod.fst (instantiateLevelsA_piTelA ls fv.idxTelA
    (piTelA fv.indices (.sort fv.sort) (.succ fv.sort)).2 fv.params)
  simp only at h
  rw [fv.stored, piTelA_append]
  show applyTelA ps (instantiateLevelsA ls (piTelA fv.params fv.idxTelA _).1) = _
  rw [h, ← substA_id (piTelA _ _ _).1]
  exact applyTelA_piTelA _ _ _ ps (by simp [instDomsA, hps, fv.nparams]) SubstA.id

theorem CtorViewA.mirrors_length {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) :
    v.mirrors.length = fm.nparamsA :=
  v.mirrorsConv.length.trans fv.nparams

/-- the constructor's family is `f` (`memberFamRefA`). -/
theorem CtorViewA.famRef {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm) :
    memberFamRefA cm = some f := by
  unfold memberFamRefA
  rw [v.stored]
  exact spineHeadRefA_piBodyA_ctorTypeA _ _ _ _ _ _

theorem FieldA.noDelta_instLevels (ls : List Level) {x : FieldA} (hx : x.NoDelta) :
    (x.instLevels ls).NoDelta := by
  cases x <;> first | trivial | exact hx.elim

theorem FieldA.norm_instLevels (ls : List Level) (x : FieldA) :
    (x.instLevels ls).norm = x.norm.instLevels ls := by
  cases x <;> rfl

theorem FieldA.norm_freeOf {f : Nat} (x : FieldA) : x.norm.FreeOf f ↔ x.FreeOf f := by
  cases x <;> exact Iff.rfl

theorem CtorViewA.freeOf {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm)
    (hfresh : E.members f = none) :
    (∀ x ∈ v.fields, x.FreeOf f) ∧ ∀ a ∈ v.res, FreeOfA f a :=
  v.typed.freeOf hfresh

/-- a view's instantiated NORMED fields carry no δ-marker — `norm` erases `drecD` to `drec`
    before `instLevels` sees it (R-NoDeltaRec-4d-iii). -/
theorem CtorViewA.norm_noDelta_instLevels {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm)
    (ls : List Level) :
    ∀ x ∈ (v.fields.map FieldA.norm).map (FieldA.instLevels ls), x.NoDelta := fun _ hy => by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
  exact FieldA.noDelta_instLevels ls (FieldA.norm_noDelta y)

/-- the kinds ι's correspondence with `main` reads are the view's — read off the NORMED type,
    where a δ-reached field is the family application (R-NoDeltaRec-4d-iii). -/
theorem CtorViewA.kinds {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm)
    (hfresh : E.members f = none) (hnf : ∀ x ∈ v.fields, x.NoFun) :
    ctorKindsA f fm.nparamsA (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors
        (v.fields.map FieldA.norm) v.res) = some (v.fields.map FieldA.kind) := by
  have hfree : ∀ x ∈ v.fields.map FieldA.norm, x.FreeOf f := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (FieldA.norm_freeOf y).mpr ((v.freeOf hfresh).1 y hy)
  have htf : ∀ x ∈ v.fields.map FieldA.norm, x.TreeField := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact FieldA.treeField_of ((FieldA.norm_noFun y).mpr (hnf y hy)) (FieldA.norm_noDelta y)
  have hk := ctorKindsA_ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors
    (v.fields.map FieldA.norm) v.res hfree htf
  refine (v.mirrors_length ▸ hk).trans (congrArg some ?_)
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  exact FieldA.norm_kind x

/-- the shapes the relation reads are the view's — read off the NORMED type (`ctorShapesA`
    through erasure; the stored type's δ-reached domain is not a syntactic family application,
    `drCtorShapesA_none`). -/
theorem CtorViewA.shapes {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm)
    (hfresh : E.members f = none) :
    ctorShapesA f fm.nparamsA (ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors
        (v.fields.map FieldA.norm) v.res) = some (v.fields.map FieldA.shape) := by
  have hfree : ∀ x ∈ v.fields.map FieldA.norm, x.FreeOf f := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact (FieldA.norm_freeOf y).mpr ((v.freeOf hfresh).1 y hy)
  have hnd : ∀ x ∈ v.fields.map FieldA.norm, x.NoDelta := fun x hx => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
    exact FieldA.norm_noDelta y
  have hs := ctorShapesA_ctorTypeA f (canonLevelsA fm.arity) fv.sort v.mirrors
    (v.fields.map FieldA.norm) v.res hfree hnd
  refine (v.mirrors_length ▸ hs).trans (congrArg some ?_)
  rw [List.map_map]
  apply List.map_congr_left
  intro x hx
  exact FieldA.norm_shape x

/-- THE CONSTRUCTOR AT ITS PARAMETERS: the instantiated constructor type applied to
    `nparamsA` arguments is the field telescope at the state `(ps, consListA ps id)`. -/
theorem CtorViewA.applyTel_params {fv : FamViewA fm} (v : CtorViewA E I f fm fv cm)
    (ls : List Level) (hls : ls.length = fm.arity) (ps : List ExprA)
    (hps : ps.length = fm.nparamsA) :
    applyTelA ps (instantiateLevelsA ls cm.mtypeA) =
      some (ctorFieldsA f ls (instLevel ls fv.sort) ps (consListA ps SubstA.id)
        (v.fields.map (FieldA.instLevels ls)) (v.res.map (instantiateLevelsA ls))).1 := by
  have hc : (canonLevelsA fm.arity).map (instLevel ls) = ls := by
    rw [← hls]; exact canonLevelsA_instLevel ls
  rw [v.stored, instantiateLevelsA_ctorTypeA, hc]
  exact applyTelA_ctorTypeA_params _ _ _ _ _ _ ps
    (by simp [instDomsA, hps, v.mirrors_length])

end ViewLaws

/-! ## (5) the group -/

/-- a constructor of the group: its reference and member, the member checks of `EnvWfA` at the
    ConstructorScope (base + the family), and its view. The parameter count is the family's
    (`FamViewA.nparams`); the constructor member's own is `0`, as at every non-family member. -/
structure GroupCtorA (I : IotaIfaceA) (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA)
    (fv : FamViewA fm) : Type where
  ref : Nat
  member : CheckedMemberA
  hcls : member.mclass = .constructorM
  hnobody : member.bodyA = none
  harity : member.arity = fm.arity
  hnp : member.nparamsA = 0
  hclT : ∀ k, liftA k 1 member.mtypeA = member.mtypeA
  u : Level
  hT : HasTyA (extendEnvA E f fm) I member.arity [] member.mtypeA (.sort u)
  hlvl : exprLevelsBoundedA member.arity member.mtypeA = true
  view : CtorViewA E I f fm fv member
  /-- `normA` carries the view-built type with each δ-reached field read as the family
      application at its indices (R-NoDeltaRec-3a/4d-iii): `ctorMemberA` sets it and every group
      constructor carries it — it is the form ι's readers consume. -/
  hnorm : member.normA = some (ctorTypeA f (canonLevelsA fm.arity) fv.sort view.mirrors
      (view.fields.map FieldA.norm) view.res)
  /-- the normed type's own closedness — it is not the stored type once δ-reached fields land
      (R-NoDeltaRec-4d-iii). -/
  hclN : ∀ k, liftA k 1 (ctorTypeA f (canonLevelsA fm.arity) fv.sort view.mirrors
      (view.fields.map FieldA.norm) view.res) =
    ctorTypeA f (canonLevelsA fm.arity) fv.sort view.mirrors (view.fields.map FieldA.norm)
      view.res
  /-- the normed type's own level bound — `member.arity` is `fm.arity` by `harity`. -/
  hlvlN : exprLevelsBoundedA member.arity (ctorTypeA f (canonLevelsA fm.arity) fv.sort
      view.mirrors (view.fields.map FieldA.norm) view.res) = true

/-- `normA.getD mtypeA` is the normed type — unconditional now that `hnorm` is a `some`
    assertion (R-NoDeltaRec-4d-iii); a δ-reached domain is read there as the family
    application. -/
theorem GroupCtorA.normA_getD {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) :
    c.member.normA.getD c.member.mtypeA =
      ctorTypeA f (canonLevelsA fm.arity) fv.sort c.view.mirrors (c.view.fields.map FieldA.norm)
        c.view.res := by
  rw [c.hnorm]
  rfl

/-- `normA.getD`'s closedness (R-NoDeltaRec-4d-iii): `hclN` transported to the getD side. -/
theorem GroupCtorA.normA_getD_closed {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) (k : Nat) :
    liftA k 1 (c.member.normA.getD c.member.mtypeA) = c.member.normA.getD c.member.mtypeA := by
  rw [c.normA_getD]; exact c.hclN k

/-- `normA.getD`'s level bound (R-NoDeltaRec-4d-iii). -/
theorem GroupCtorA.normA_getD_levels {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) :
    exprLevelsBoundedA c.member.arity (c.member.normA.getD c.member.mtypeA) = true := by
  rw [c.normA_getD]; exact c.hlvlN

/-- the normed constructor's type at `ls`: the mirrors' telescope over the NORMED fields
    (R-NoDeltaRec-4d-iii — the δ-reached fields are the family application there). -/
theorem GroupCtorA.inst_tel {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (c : GroupCtorA I E f fm fv)
    (ls : List Level) (hls : ls.length = fm.arity) :
    instantiateLevelsA ls (c.member.normA.getD c.member.mtypeA) =
      ctorTypeA f ls (instLevel ls fv.sort) (instDomsA ls c.view.mirrors)
        ((c.view.fields.map FieldA.norm).map (FieldA.instLevels ls))
        (c.view.res.map (instantiateLevelsA ls)) := by
  have hc : (canonLevelsA fm.arity).map (instLevel ls) = ls := by
    rw [← hls]; exact canonLevelsA_instLevel ls
  rw [c.normA_getD, instantiateLevelsA_ctorTypeA, hc]



/-- THE CONSTRUCTOR AT ITS PARAMETERS, OFF THE NORMED TYPE — the form the ι machinery consumes
    (R-NoDeltaRec-4d-iii): the field telescope of the normed fields, instantiated. -/
theorem GroupCtorA.applyTel_params {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat}
    {fm : CheckedMemberA} {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) (ls : List Level)
    (hls : ls.length = fm.arity) (ps : List ExprA) (hps : ps.length = fm.nparamsA) :
    applyTelA ps (instantiateLevelsA ls (c.member.normA.getD c.member.mtypeA)) =
      some (ctorFieldsA f ls (instLevel ls fv.sort) ps (consListA ps SubstA.id)
        ((c.view.fields.map FieldA.norm).map (FieldA.instLevels ls))
        (c.view.res.map (instantiateLevelsA ls))).1 := by
  rw [c.normA_getD]
  have hc : (canonLevelsA fm.arity).map (instLevel ls) = ls := by
    rw [← hls]; exact canonLevelsA_instLevel ls
  rw [instantiateLevelsA_ctorTypeA, hc]
  exact applyTelA_ctorTypeA_params _ _ _ _ _ _ ps
    (by simp [instDomsA, hps, c.view.mirrors_length])


/-- a group constructor's environment entry. -/
def GroupCtorA.entry {I : IotaIfaceA} {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}
    {fv : FamViewA fm} (c : GroupCtorA I E f fm fv) : Nat × CheckedMemberA :=
  (c.ref, c.member)

/-- the environment after a group: the family at `f`, then its constructors (the list's head
    added last). -/
def groupEnvA (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) :
    List (Nat × CheckedMemberA) → ResolvedEnvA
  | [] => extendEnvA E f fm
  | c :: cs => extendEnvA (groupEnvA E f fm cs) c.1 c.2

/-- the group's references fresh one by one: the family in the base, each constructor in the
    environment built before it. -/
def GroupFreshA (E : ResolvedEnvA) (f : Nat) (fm : CheckedMemberA) :
    List (Nat × CheckedMemberA) → Prop
  | [] => E.members f = none
  | c :: cs => GroupFreshA E f fm cs ∧ (groupEnvA E f fm cs).members c.1 = none

section GroupEnv
variable {E : ResolvedEnvA} {f : Nat} {fm : CheckedMemberA}

theorem GroupFreshA.base : {cs : List (Nat × CheckedMemberA)} → GroupFreshA E f fm cs →
    E.members f = none
  | [], h => h
  | _ :: _, h => GroupFreshA.base h.1

theorem prefixA_groupEnvA : {cs : List (Nat × CheckedMemberA)} → GroupFreshA E f fm cs →
    PrefixA E (groupEnvA E f fm cs)
  | [], h => prefixA_extend E f fm h
  | c :: _, h => prefixA_trans (prefixA_groupEnvA h.1) (prefixA_extend _ c.1 c.2 h.2)

/-- a member of the group's environment is the family, one of the constructors, or a base
    member. -/
theorem members_groupEnvA :
    (cs : List (Nat × CheckedMemberA)) → (r : Nat) → (m : CheckedMemberA) →
    (groupEnvA E f fm cs).members r = some m →
    (r = f ∧ m = fm) ∨ (r, m) ∈ cs ∨ E.members r = some m
  | [], r, m, h => by
      by_cases hr : r = f
      · subst hr
        rw [groupEnvA, members_extendEnvA_self] at h
        exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
      · rw [groupEnvA, members_extendEnvA_ne E f fm hr] at h
        exact Or.inr (Or.inr h)
  | c :: cs, r, m, h => by
      by_cases hr : r = c.1
      · subst hr
        rw [groupEnvA, members_extendEnvA_self] at h
        cases h
        exact Or.inr (Or.inl (List.mem_cons_self _ _))
      · rw [groupEnvA, members_extendEnvA_ne _ c.1 c.2 hr] at h
        rcases members_groupEnvA cs r m h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
        · exact Or.inr (Or.inr h)

theorem groupEnvA_family : (cs : List (Nat × CheckedMemberA)) → GroupFreshA E f fm cs →
    (groupEnvA E f fm cs).members f = some fm
  | [], _ => members_extendEnvA_self E f fm
  | c :: cs, h => by
      have hf := groupEnvA_family cs h.1
      have hne : f ≠ c.1 := fun he => by
        have h2 := h.2
        rw [← he, hf] at h2
        exact Option.noConfusion h2
      rw [groupEnvA, members_extendEnvA_ne _ c.1 c.2 hne, hf]

end GroupEnv

#print axioms consListA_add
#print axioms paramLocalsA_consListA
#print axioms applyTelA_piTelA
#print axioms applyTelA_ctorFieldsA
#print axioms substA_ctorFieldsA
#print axioms piTelA_append
#print axioms applyTelA_ctorTypeA
#print axioms applyTelA_ctorTypeA_params
#print axioms instantiateLevelsA_ctorTypeA
#print axioms canonLevelsA_instLevel
#print axioms ctorKindsA_ctorTypeA
#print axioms ctorShapesA_ctorTypeA
#print axioms frecDomA_eq
#print axioms substA_frecDomA
#print axioms instantiateLevelsA_frecDomA
#print axioms fieldShapeE_frecDomA
#print axioms fieldShapesE_ctorFieldsA
#print axioms spineHeadRefA_piBodyA_ctorTypeA
#print axioms FamViewA.applyTel_params
#print axioms FamViewA.isArity
#print axioms CtorViewA.famRef
#print axioms CtorViewA.kinds
#print axioms CtorViewA.shapes
#print axioms map_shape_instLevels
#print axioms CtorViewA.applyTel_params
#print axioms members_groupEnvA
#print axioms prefixA_groupEnvA
#print axioms FieldA.map_norm_self

/-! ## (6) the small-index profile (moved from `RcicAnnFamHeight`, M2-f (4b)) -/

/-- the sort levels of a telescope's binder domains (each Π's domain annotation). -/
def piDomLevelsA : ExprA → List Level
  | .pi _ u B _ => u :: piDomLevelsA B
  | _ => []

/-- THE SMALL-INDEX PROFILE (M2-f (3c); a NEW research-scope condition, not a consequence of
    05): under every valuation at which a family's result sort is not `Prop`, every INDEX binder
    of the family — a binder after its `nparamsA` parameters — has its domain's sort at most the
    family's sort. Where the sort is `Prop` the application is a proposition (`TyKA.prop`
    reads it, `EqKA.stuck` can equate it), and no index walk is needed. The families' clause
    (M2-f (4b)) carries this as a premise. -/
def SmallIndexProfileA (E : ResolvedEnvA) : Prop :=
  ∀ (r : Nat) (m : CheckedMemberA) (u₀ : Level), E.members r = some m → m.mclass = .inductiveM →
    piBodyA m.mtypeA = .sort u₀ → ∀ v ∈ (piDomLevelsA m.mtypeA).drop m.nparamsA,
      ∀ (ρ : Nat → Option Nat) (x y : Nat), eval ρ v = some x → eval ρ u₀ = some y → 0 < y → x ≤ y

end Rcic.Declarative.Ann
