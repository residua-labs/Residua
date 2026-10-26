/-
Class-A boundary measurement (F3 route-c, lane devin-fcd 2026-10-24):
the exact non-IR condition on admitted constructor telescopes, stated
over the admission structures as checkable syntax.

CONTEXT.  Route (i) class A (W-types, swe-rk01-logrel-a) admits a
constructor field domain that depends on parameters, indices, and
earlier NON-recursive fields, and on recursive fields only through
Prop-typed fields.  The measured boundary is the induction–recursion
shape: a recursive field `j` whose decoded value feeds the domain of a
LATER field `k` (`mk : (x : T) → (P x : Type) → T` with `P` applied to
the recursive `x`).

FINDING.  `EnvWfT` admits no field domain that free-references an
earlier recursive field — the boundary is EMPTY, in the strong form
(the spec's Prop exception is vacuous).  Every consumption route for
`x : F as` inside a field domain is walled, each wall pinned to code:

  W1  Bare `y : x`: `fields[j]` is canonical `Π doms, F app` — whnf
      head `const fam` is neutral (family members carry no body), so
      `Conv (fields[j]) (.sort _)` fails; `HasTy (bvar→j) (sort lv)`
      cannot type the domain.
  W2  `A_k = app g (bvar→j)`: needs `g : Π (z : D), _` with
      `Conv D (fields[j])`; `D`'s whnf must expose `const fam`.
      Every position of `g` is excluded:
        - family/constructor parameter: parameter domains are fam-free
          (`parameterMirrors` — they mirror the family's, typed before
          `fam` existed);
        - earlier field: fam-free inner domains by `domainsContainFuel`
          (a `Π (z : F _), _` field is `refused .negativeOccurrence`);
        - inner binder inside `A_k` itself: `containsFamilyFuel` scans
          inner Π/λ/let domains, so `fam` under `g`'s domain makes
          `A_k` non-fam-free — field `k` is refused or recursive,
          never a fam-free domain carrying the reference;
        - earlier constructor `c_i`: `c_i x : F _` — an `F _`-typed
          term reaches a `sort`-typed position only through a further
          `F _ → sort` consumer; same wall;
        - `const m`: `m.mtype` must mention `fam`; group order admits
          `fam`, then ctors, then `rr` — a fam-mentioning member type
          cannot precede `fam`, and `rr` follows all ctors.
  W3  Sort-polymorphic consumers (`Eq`-style `Π (α : Sort u), …`):
      passing `x : F as` writes the literal `F as` instantiation into
      `A_k` (`app (app (const Eq) (F-as-expr)) x`) — `containsFamilyFuel`
      sees `const fam` in the syntax → `k` not fam-free.
  W4  Inside `A_k`'s own recursive codomain `F bs`: an argument
      `(bvar→j)` needs `Conv (fields[j]) (index domain)` — index
      domains are fam-free (`indicesCleanFuel` / `noFamilyInIndices`)
      → refused.  `famFreeArgs` independently refuses a recursive
      codomain argument mentioning `fam`.
  W5  `Conv` cannot launder `fields[j]`: `const fam`-headed whnf is
      neutral, so every convertible expression has `const fam` in its
      normal form — `fields[j]` is never `Conv` to a fam-free or
      `sort`-headed type.

CENSUS (measured; details in the research note +
~/.residua-fable-f3cover/PROGRESS.md): importer slice corpus
(`slice2_closed`) and Init export (`init_nat_list_211`): 0 hits — all
nine detected earlier-field dependencies land on non-recursive fields
(Char.mk, Exists.intro, Nat.le.step, Nat.le.below.step, Fin.mk,
PSigma.mk, Acc.intro, WellFoundedRelation.mk).  R-CIC fixtures: every
bvar-dependent field domain resolves to a parameter-typed or
nonrecursive entry (`tl : Vec A n` mentions `n : Nat`; `hd : A`;
`y : x` with `x` param-typed).

NAMED RESIDUE — the theorem `∀ admitted group → NonIRFieldList`
(machine form of "EnvWfT → non-IR") is stated but unproved here.  Its
proof needs (i) `HasTy` inversion on application spines, (ii) a
`Conv`/whnf lemma that a `const fam`-headed normal form is never
convertible to a fam-free or sort-headed expression, (iii) the
member-timing of the group order `fam ≺ ctors ≺ rr`.  None of the
three exists on the tree; the boundary condition is landed below as
kernel-checked syntax plus computational pins.  `closure_claim = 0`.
-/

import rcic.RcicInductivePolicy

namespace Rcic.Declarative

/-! ## Free de Bruijn occurrence scan -/

/-- `freeBvarRef base d e`: `.bvar (base + d)` occurs free in `e`,
    where `d` counts binders opened inside `e` itself.  At depth 0
    this is "the local `base` slots below the context top occurs". -/
def freeBvarRef (base d : Nat) : Expr Nat → Bool
  | .bvar i => decide (i = base + d)
  | .sort _ => false
  | .lit _ => false
  | .const _ _ => false
  | .app g a => freeBvarRef base d g || freeBvarRef base d a
  | .lam A B => freeBvarRef base d A || freeBvarRef base (d + 1) B
  | .pi A B => freeBvarRef base d A || freeBvarRef base (d + 1) B
  | .letE A v B =>
      freeBvarRef base d A || freeBvarRef base d v ||
      freeBvarRef base (d + 1) B

/-- Field `k`'s domain `A` free-references earlier field `j` (for
    `j < k`): `.bvar (k-1-j)` at depth 0, i.e. `.bvar (k-1-j+d)` under
    `d` inner binders of `A`.  In `policyPi (parameters ++ fields)` the
    context entry for field `j` sits `k-1-j` slots below the top of
    `policyPrefixContext … (np + k)`. -/
def fieldDep (k j : Nat) (A : Expr Nat) : Bool :=
  freeBvarRef (k - 1 - j) 0 A

/-! ## The boundary condition -/

/-- `A` mentions the family where the admission scanner sees it —
    `containsFamilyFuel` is δ-transparent (it unfolds transparent
    bodies).  `containsFamilyFuel_mono` makes the detecting fuels
    upward closed, so `∃ fuel` is the fuel-free notion.  Wider than
    "classified `.recursive`": any family occurrence counts. -/
def FamilyVisible (E : ResolvedEnv) (fam : Nat) (A : Expr Nat) : Prop :=
  ∃ fuel, containsFamilyFuel E fam fuel A = some true

/-- A literal family head is visible with one unit of fuel. -/
theorem familyVisible_const {E : ResolvedEnv} {fam : Nat}
    {ls : List Level} : FamilyVisible E fam (.const fam ls) := by
  refine ⟨1, ?_⟩
  simp only [containsFamilyFuel]
  rw [if_true]

/-- The class-A boundary on one stored field list: no field domain
    free-references an earlier field whose own domain mentions the
    family.  Stronger than the spec statement — the Prop exception is
    dropped (the walls make it vacuous). -/
def NonIRFieldList (E : ResolvedEnv) (fam : Nat)
    (fields : List (Expr Nat)) : Prop :=
  ∀ (j k : Fin fields.length), j.val < k.val →
    FamilyVisible E fam fields[j.val] →
    freeBvarRef (k.val - 1 - j.val) 0 fields[k.val] = false

/-- View-level form: the constructor's field list is non-IR. -/
def PolicyConstructorView.NonIR {E : ResolvedEnv}
    {family : PolicyFamilyView E} {member : CheckedMember}
    (c : PolicyConstructorView E family member) : Prop :=
  NonIRFieldList E family.ref c.fields

/-- Spec-exact form including the Prop exception: a reference to an
    earlier family-mentioning field may occur only inside a Prop-level
    field domain.  `NonIR` implies it trivially. -/
def PolicyConstructorView.NonIRSpec {E : ResolvedEnv}
    {family : PolicyFamilyView E} {member : CheckedMember}
    (c : PolicyConstructorView E family member) : Prop :=
  ∀ (j k : Fin c.fields.length), j.val < k.val →
    FamilyVisible E family.ref c.fields[j.val] →
    freeBvarRef (k.val - 1 - j.val) 0 c.fields[k.val] = true →
    UniformProp (c.fieldLevel k)

theorem PolicyConstructorView.nonIR_imp_spec {E : ResolvedEnv}
    {family : PolicyFamilyView E} {member : CheckedMember}
    {c : PolicyConstructorView E family member}
    (h : c.NonIR) : c.NonIRSpec := by
  intro j k hlt hvis hdep
  have hno := h j k hlt hvis
  rw [hdep] at hno
  exact absurd hno (by decide)

/-- Group-level form: every constructor view of an admitted group is
    non-IR.  `EnvWfT → non-IR` is this universally quantified
    statement over `RecursorEliminationAdmitted` — the named residue
    (module docstring). -/
def RecursorEliminationAdmitted.NonIR {E : ResolvedEnv} {r : Nat}
    {m : CheckedMember} (a : RecursorEliminationAdmitted E r m) : Prop :=
  ∀ i : Fin a.constructors.length,
    NonIRFieldList E a.family.ref (a.constructorViews i).fields

/-! ## Refutation helpers and pins -/

/-- `emptyEnv` carries no transparent bodies: every const resolves
    to `none` under `transparentBody`. -/
theorem transparentBody_empty (r : Nat) (ls : List Level) :
    transparentBody emptyEnv r ls = none := rfl

/-- A non-family const is never family-visible in `emptyEnv`. -/
theorem not_familyVisible_const_ne {fam r : Nat} (h : r ≠ fam) :
    ¬ FamilyVisible emptyEnv fam (.const r []) := by
  rintro ⟨fuel, hf⟩
  cases fuel with
  | zero => exact Option.noConfusion hf
  | succ f =>
      have hs : containsFamilyFuel emptyEnv fam (f + 1) (.const r []) =
          some false := by
        simp only [containsFamilyFuel]
        rw [if_neg h, transparentBody_empty]
      rw [hs] at hf
      exact absurd hf (by decide)

/-- A bound variable is never family-visible. -/
theorem not_familyVisible_bvar {fam i : Nat} :
    ¬ FamilyVisible emptyEnv fam (.bvar i) := by
  rintro ⟨fuel, hf⟩
  cases fuel with
  | zero => exact Option.noConfusion hf
  | succ f =>
      rw [show containsFamilyFuel emptyEnv fam (f + 1) (.bvar i) =
          some false from rfl] at hf
      exact absurd hf (by decide)

/-- Detection pin: the exact IR shape `mk : (x : F) → (P x : Type) → F`
    violates `NonIRFieldList` — field 1's domain `P x` free-references
    the recursive field 0.  Family at ref 4, `P` at ref 9. -/
theorem nonIR_refused_ir_shape :
    ¬ NonIRFieldList emptyEnv 4
      [.const 4 [], .app (.const 9 []) (.bvar 0)] := by
  intro h
  have hdep := h ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    familyVisible_const
  exact absurd hdep (by decide)

/-- Permission pin: `vcons`'s field list — `n : Nat`, `hd : A`,
    `tl : Vec A n` — satisfies the boundary even though `tl`'s domain
    free-references `n`.  `n : Nat` carries no family occurrence, so
    every `FamilyVisible` premise is refuted. -/
theorem nonIR_permitted_vec_shape :
    NonIRFieldList emptyEnv 4
      [.const 0 [], .bvar 1,
       .app (.app (.const 4 []) (.bvar 2)) (.bvar 1)] := by
  intro j k hlt hvis
  obtain ⟨jv, hjv⟩ := j
  obtain ⟨kv, hkv⟩ := k
  have hj3 : jv < 3 := hjv
  have hk3 : kv < 3 := hkv
  have hlt' : jv < kv := hlt
  rcases jv with _ | _ | _ | jv3
  · rcases kv with _ | _ | _ | kv3
    · omega
    · exact absurd hvis (not_familyVisible_const_ne (by decide))
    · exact absurd hvis (not_familyVisible_const_ne (by decide))
    · omega
  · rcases kv with _ | _ | _ | kv3
    · omega
    · omega
    · exact absurd hvis not_familyVisible_bvar
    · omega
  · rcases kv with _ | _ | _ | kv3
    · omega
    · omega
    · omega
    · omega
  · omega

/-- `fieldAnalyze` classification pin: a bare family application is
    `.recursive 0` — `FamilyVisible` over-approximates this class. -/
theorem fieldAnalyze_const_fam_recursive :
    fieldAnalyze emptyEnv 6 4 0 0 0 0 (.const 4 []) =
      .permitted (.recursive 0) [] := by
  decide

/-- `fieldAnalyze` classification pin: a function-recursive field
    domain `B → F` (the W-type shape) is permitted `.recursive 1` —
    fam-free inner domain, canonical codomain. -/
theorem fieldAnalyze_pi_recursive_one :
    fieldAnalyze emptyEnv 6 4 0 0 0 0
      (.pi (.const 0 []) (.const 4 [])) =
      .permitted (.recursive 1) [] := by
  decide

/-- `fieldAnalyze` refutation pin: `F → anything` as a field domain is
    refused `negativeOccurrence` — the W2 wall for an inner binder
    whose domain mentions the family. -/
theorem fieldAnalyze_pi_dom_fam_refused :
    fieldAnalyze emptyEnv 6 4 0 0 0 0
      (.pi (.const 4 []) (.const 0 [])) =
      .refused .negativeOccurrence := by
  decide

end Rcic.Declarative
