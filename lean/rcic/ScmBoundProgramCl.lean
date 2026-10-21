/-
RCIC 06 §18 SCM-015 — `ProgramBundleAt` over the multi-group closure
(cc on #6568: "ProgramBundleAt means §18's transitive closure … build the
multi-group proposition, with external FunctionRef resolution across the
bundle's groups, plus its carrier. The one-group prop stays as the special
case. Prove they agree on ext = [] bundles; never edit the sealed one.")

Owner text: 06 §7 "A closed core-program bundle contains the root, residue
catalog, and the exact transitive closure of function groups and profiles";
§17 decode step 2 "decode signatures and resolve external refs"; §18 "The
bundle witness is mandatory because execution needs all transitive function
groups, the residue catalog, and profiles"; 01 §4 `FunctionRef { group_ref,
member_index }`, "Member indices are bounds-checked; there is no modulo or
member-zero fallback."

The one-group `ProgramAtAt`/`ProgramBundleAt` of `ScmBoundProgramAt` is NOT
touched: `programAtAtCl_of_programAtAt` and
`programAtAt_of_programAtAtCl` below prove this closure agrees with it on
one-group `ext = []` bundles.

TRANSCRIPTION TABLE (06 → Lean):
  §17 step 2 resolve external refs                → `extResolves`: every
        signature in every group's ext table names a member of a group in
        `gs` — the serialized `FunctionRef` `encStr (dg g' 19) ++ encNat m`
        hits that group's kind-19 digest and a member index in range — and
        the callee's signature agrees
  §7/§18 exact transitive closure of function groups → `closureSet`:
        every `g ∈ gs` has `dg g 19` reachable from the entry group's
        digest over resolved ext edges (minimality: no unreferenced
        member); `extResolves` is the closure half (no dangling edge).
        `extStep`/`ReachCl` are the declarative reading
  §18 one-group `program_bundle_at` special case  → `ProgramAtAt`;
        `programAtAtCl_of_programAtAt` / `programAtAt_of_programAtAtCl`
  §17 step 4 exact typed signatures and bodies    → per-group `elabBodies`
        under the group's own signature scope and the shared catalog
        (`catalogOf bcat`)
  [spec_ambiguity] the serialized `FunctionRef`'s byte form — 06/01 give no
        format. `encFnRef d m = encStr d ++ encNat m` is the smallest
        content-addressed reading: the group is named by the same kind-19
        content digest the root's entry `FunctionRef` carries, the member
        index is the §4 bound-checked U64.
-/

import rcic.ScmBoundProgramAt

namespace Rcic.Scm.BoundProgAt
open Rcic.Scm Rcic.Scm.BoundProg Rcic.Scm.Wire Rcic.BoundObject

/-- The kind-`k` content digest of `b` (the pins files' `dg` helper). -/
def dg (b : String) (k : Int) : String := Rcic.TypedRef.deriveDigest 3 k b

/-! ## The serialized external `FunctionRef` -/

/-- The complete `FunctionRef` written as an ext-table `ref`: the callee
    group's kind-19 content digest under `encStr`, the member index under
    `encNat`. -/
def encFnRef (digest : String) (m : Int) : String := encStr digest ++ encNat m

/-- Parse an `encFnRef`: an `encStr` prefix, then an `encNat` that consumes
    the rest exactly. -/
def decFnRef (s : String) : Option (String × Int) :=
  let cs := s.toList.toArray
  match decStr cs 0 with
  | .error _ => none
  | .ok (d, q) =>
    match decNat cs q with
    | .error _ => none
    | .ok (m, q') => if q' = cs.size then some (d, m) else none

/-! ## One decoded group of the closure -/

/-- A group's digest-graph view: its kind-19 content digest, its declared
    profile, ext table and functions. -/
structure ClGroup where
  bytes : String
  digest : String
  prg : String
  ext : List ExtSig
  fns : List RawFnDef

/-- `e` resolves to member `m'` of `g'` (ref serializes that FunctionRef
    and the callee's signature agrees). -/
def resolvesTo (g' : ClGroup) (e : ExtSig) (m' : Nat) : Bool :=
  e.ref == encFnRef g'.digest m' &&
  match g'.fns.get? m' with
  | some fn' => decide (fn'.params = e.params) && decide (fn'.result = e.result)
  | none => false

/-- `e` resolves somewhere in `gs`. -/
def extSigResolves (gs : List ClGroup) (e : ExtSig) : Bool :=
  gs.any fun g' => (List.range g'.fns.length).any fun m' => resolvesTo g' e m'

/-- Every signature in `g`'s ext table resolves inside `gs`. -/
def groupExtResolves (gs : List ClGroup) (g : ClGroup) : Bool :=
  g.ext.all fun e => extSigResolves gs e

/-- The digests `g`'s ext table resolves to (the out-edges). -/
def extTargets (gs : List ClGroup) (g : ClGroup) : List String :=
  gs.filterMap fun g' =>
    if g.ext.any fun e => (List.range g'.fns.length).any fun m' => resolvesTo g' e m'
    then some g'.digest else none

/-! ## The closure computation -/

/-- One expansion pass over the seen set: every group's digest already
    seen contributes its resolved target digests. -/
def reachStep (gs : List ClGroup) (seen : List String) : List String :=
  gs.foldl (fun acc g =>
    if g.digest ∈ seen then acc ++ extTargets gs g else acc) seen

/-- `n` expansion passes over the seen set. -/
def reachSteps (gs : List ClGroup) : Nat → List String → List String
  | 0, s => s
  | n + 1, s => reachStep gs (reachSteps gs n s)

/-- The reachable digest set from `entry` over the bundle's ext edges:
    `|gs|` expansion passes from `{entry}` — every simple path is at most
    `|gs|` long. -/
def closureSet (gs : List ClGroup) (entry : String) : List String :=
  reachSteps gs gs.length [entry]

/-- The decoded-group view of a group list (`decode` gives the shape; the
    prop's binding conjunct already supplies `CanonicalObjectAt`). -/
def clGroups (profile : String) (gs : List String) : List ClGroup :=
  gs.map fun g =>
    match (objSchema 19 profile).decode g with
    | some (.group prg ext fns) => ⟨g, dg g 19, prg, ext, fns⟩
    | _ => ⟨g, dg g 19, "", [], []⟩

/-! ## `ProgramAtAtCl` — the multi-group closure as a proposition -/

/-- The declarative ext-edge: a group in `gs` at digest `src` declares an
    ext signature whose ref serializes `{dst, m}` (06 §7 "transitive
    closure" reading; `closureSet` is the computed version). -/
def extStep (profile : String) (gs : List String) (src dst : String) : Prop :=
  ∃ g prg ext fns, g ∈ gs ∧ dg g 19 = src ∧
    (objSchema 19 profile).decode g = some (.group prg ext fns) ∧
    ∃ e m, e ∈ ext ∧ e.ref = encFnRef dst m

/-- `dst` is reachable from `src` over the bundle's ext edges. -/
inductive ReachCl (profile : String) (gs : List String) : String → String → Prop
  | refl (src : String) : ReachCl profile gs src src
  | step (src mid dst : String) : extStep profile gs src mid → ReachCl profile gs mid dst →
      ReachCl profile gs src dst

/-- The external-resolution conjunct (06 §17 step 2): every signature in
    every group's ext table names a member of a group in `gs` — the
    serialized `FunctionRef` hits that group's kind-19 digest and a member
    index in range — and the callee's signature agrees. Stated over the
    decoded `clGroups` view: `m'` is a `Nat`, so a negative member index
    can never resolve (01 §4 "no member-zero fallback"). -/
def extResolves (profile : String) (gs : List String) : Prop :=
  ∀ cg ∈ clGroups profile gs, ∀ e ∈ cg.ext, ∃ cg' ∈ clGroups profile gs,
    ∃ m' : Nat, e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
    ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧ fn'.result = e.result

/-- The multi-group closure at program-check fuel `F`, in `ProgramAtAt`'s
    ∃-decode style: the root decodes to a program root, the bundle to a
    group list over the root's bytes (exactness itself is
    `P.bundle_root_exact`), the catalog the root names binds canonically,
    the group list is non-empty and duplicate-free, every group binds
    under the profile, the root's entry `FunctionRef` names a member of
    the bundle, every ext ref resolves inside `gs`, every group's digest
    is reachable from the entry group's (the exact transitive closure),
    and every group's bodies elaborate under its own signature scope and
    the shared catalog. -/
def ProgramAtAtCl {profile : String} (F : Int) (P : BoundCoreProgram profile) : Prop :=
  ∃ pr cat grp m broot bcat gs,
    (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m) ∧
    (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs) ∧
    CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat ∧
    gs ≠ [] ∧ gs.Nodup ∧
    (∀ cg ∈ clGroups profile gs,
      CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, cg.digest⟩ cg.bytes ∧
      (objSchema 19 profile).decode cg.bytes = some (.group cg.prg cg.ext cg.fns)) ∧
    (∃ cg ∈ clGroups profile gs,
      cg.digest = grp ∧ 0 ≤ m ∧ m.toNat < cg.fns.length) ∧
    extResolves profile gs ∧
    (∀ cg ∈ clGroups profile gs, cg.digest ∈ closureSet (clGroups profile gs) grp) ∧
    (∀ cg ∈ clGroups profile gs,
      (elabBodies (fuelN F) ⟨cg.fns.map (fun f => ⟨f.params, f.result⟩), cg.ext,
        catalogOf bcat⟩ cg.fns).toOption.isSome = true)

/-- The multi-group `ProgramBundleAt` (06 §18): the bound program's closure
    over all transitive function groups holds at some program-check fuel. -/
def ProgramAtCl {profile : String} (P : BoundCoreProgram profile) : Prop :=
  ∃ F : Int, ProgramAtAtCl F P

/-- The census row's name under the cc reading (SCM-015, cc on #6568). -/
abbrev ProgramBundleAtCl {profile : String} (P : BoundCoreProgram profile) : Prop :=
  ProgramAtCl P

/-! ## `clGroups` membership -/

/-- `clGroups` members are `gs` bytes at their own kind-19 digest. -/
theorem mem_clGroups {profile : String} {gs : List String} {cg : ClGroup}
    (h : cg ∈ clGroups profile gs) :
    cg.bytes ∈ gs ∧ cg.digest = dg cg.bytes 19 := by
  simp only [clGroups, List.mem_map] at h
  obtain ⟨g, hg, hcg⟩ := h
  have hb : cg.bytes = g := by
    rw [← hcg]
    cases hde : (objSchema 19 profile).decode g with
    | none => rfl
    | some o => cases o <;> rfl
  have hd' : cg.digest = dg g 19 := by
    rw [← hcg]
    cases hde : (objSchema 19 profile).decode g with
    | none => rfl
    | some o => cases o <;> rfl
  exact ⟨hb.symm ▸ hg, hb.symm ▸ hd'⟩

/-- When a `clGroups` member's bytes decode to `.group`, its fields are the
    decoded ones. -/
theorem clGroups_fields {profile : String} {gs : List String} {cg : ClGroup}
    (h : cg ∈ clGroups profile gs) {prg : String} {ext : List ExtSig}
    {fns : List RawFnDef}
    (hd : (objSchema 19 profile).decode cg.bytes = some (.group prg ext fns)) :
    cg.prg = prg ∧ cg.ext = ext ∧ cg.fns = fns := by
  simp only [clGroups, List.mem_map] at h
  obtain ⟨g, hg, hcg⟩ := h
  have hb : cg.bytes = g := by
    rw [← hcg]
    cases hde : (objSchema 19 profile).decode g with
    | none => rfl
    | some o => cases o <;> rfl
  rw [hb] at hd
  rw [← hcg]
  cases hde : (objSchema 19 profile).decode g with
  | none =>
    have hd' : (objSchema 19 profile).decode g = some (.group prg ext fns) := hd
    rw [hde] at hd'
    exact absurd hd' (by simp)
  | some o =>
    cases o with
    | group prg' ext' fns' =>
      have hd' : (objSchema 19 profile).decode g = some (.group prg ext fns) := hd
      rw [hde] at hd'
      have h2 := Option.some.inj hd'
      injection h2 with h1 h2' h3
      subst h1; subst h2'; subst h3
      exact ⟨rfl, rfl, rfl⟩
    | _ =>
      have hd' : (objSchema 19 profile).decode g = some (.group prg ext fns) := hd
      rw [hde] at hd'
      exact absurd hd' (by simp)

/-- A `gs` member that decodes to `.group` lands in `clGroups`. -/
theorem clGroups_mem_of_mem {profile : String} {gs : List String} {g : String}
    (hg : g ∈ gs) {prg : String} {ext : List ExtSig} {fns : List RawFnDef}
    (hd : (objSchema 19 profile).decode g = some (.group prg ext fns)) :
    ⟨g, dg g 19, prg, ext, fns⟩ ∈ clGroups profile gs := by
  simp only [clGroups, List.mem_map]
  exact ⟨g, hg, by rw [hd]⟩

/-! ## Helpers for the catalog and `progCheck` conjuncts -/

/-- The canonical bound catalog the root names is a canonical catalog list —
    the conjunct `progCheck`'s own catalog gate pays. -/
theorem catalogOf_canonical {cat bcat : String}
    (h : CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat) :
    catalogCanonical (catalogOf bcat) = true := by
  obtain ⟨hd, _, _⟩ := h
  cases hdec : (objSchema 18 "").decode bcat with
  | none => rw [hdec] at hd; exact hd.elim
  | some o =>
    rw [hdec] at hd
    have hsave := hdec
    have hdec' : (match objDec (↑bcat.length) 18 bcat with
        | .ok (o', _) =>
          if (18 : Int) = 18 ∧ !catalogCanonical (objCatalog o') then none
          else some o'
        | .error _ => none) = some o := hdec
    cases ho : objDec (↑bcat.length) 18 bcat with
    | error => rw [ho] at hdec'; exact absurd hdec' (by simp)
    | ok op =>
      obtain ⟨o', p'⟩ := op
      rw [ho] at hdec'
      dsimp only at hdec'
      by_cases hc : (18 : Int) = 18 ∧ !catalogCanonical (objCatalog o')
      · rw [if_pos hc] at hdec'; exact absurd hdec' (by simp)
      · rw [if_neg hc] at hdec'
        obtain rfl := Option.some.inj hdec'
        obtain ⟨c, rfl⟩ := objDec_catalog ho
        rw [catalogOf_eq hsave]
        cases hcc : catalogCanonical c with
        | true => rfl
        | false =>
          have hnc : (!catalogCanonical (objCatalog (.catalog c))) = true := by
            show (!catalogCanonical c) = true
            simp [hcc]
          exact absurd ⟨rfl, hnc⟩ hc

/-- `progCheck` assembles `.ok` from its four gates — the direction the
    closure's per-group conjuncts pay into. -/
theorem progCheck_ok_of {F : Int} {p : RawProg} {ef : RawFnDef} {bs}
    (hcat : catalogCanonical p.catalog = true)
    (he : 0 ≤ p.entry) (hef : p.fns.get? p.entry.toNat = some ef)
    (hb : elabBodies (fuelN F) (sigOf p) p.fns = .ok bs) :
    progCheck F p = .ok ⟨bs, ef.result⟩ := by
  unfold progCheck
  rw [if_neg (by simp [hcat]), if_neg (by omega), hef]
  dsimp only
  rw [hb]
  rfl

/-! ## The `programAtClDec` instrument -/

/-- The `resolvesTo` Bool decomposed (carrier ↔ proposition bridge): the
    ref serializes `{cg'.digest, m'}`, `m'` is in range, and the callee
    member's signature agrees. -/
theorem resolvesTo_prop {cg' : ClGroup} {e : ExtSig} {m' : Nat}
    (h : resolvesTo cg' e m' = true) :
    e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
      ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧
        fn'.result = e.result := by
  unfold resolvesTo at h
  rw [Bool.and_eq_true] at h
  obtain ⟨href, hmat⟩ := h
  have hr : e.ref = encFnRef cg'.digest ↑m' := eq_of_beq href
  cases hget : cg'.fns.get? m' with
  | none => rw [hget] at hmat; cases hmat
  | some fn' =>
    rw [hget] at hmat; dsimp only at hmat
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hmat
    have hget' : cg'.fns[m']? = some fn' := by
      rw [← List.get?_eq_getElem?]; exact hget
    have hlt : m' < cg'.fns.length :=
      (List.getElem?_eq_some_iff.mp hget').1
    exact ⟨hr, hlt, ⟨fn', rfl, hmat.1, hmat.2⟩⟩

/-- The prop side pays the `resolvesTo` Bool. -/
theorem resolvesTo_of_prop {cg' : ClGroup} {e : ExtSig} {m' : Nat}
    (hr : e.ref = encFnRef cg'.digest m') (_hlt : m' < cg'.fns.length)
    {fn' : RawFnDef} (hget : cg'.fns.get? m' = some fn')
    (hp : fn'.params = e.params) (hres : fn'.result = e.result) :
    resolvesTo cg' e m' = true := by
  unfold resolvesTo
  rw [beq_iff_eq.mpr hr, hget]
  dsimp only
  rw [decide_eq_true_eq.mpr hp, decide_eq_true_eq.mpr hres]
  rfl

/-- `extSigResolves` decided yields the per-signature existential. -/
theorem extSigResolves_prop {profile : String} {gs : List String} {e : ExtSig}
    (h : extSigResolves (clGroups profile gs) e = true) :
    ∃ cg' ∈ clGroups profile gs, ∃ m' : Nat,
      e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
        ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧
          fn'.result = e.result := by
  unfold extSigResolves at h
  rw [List.any_eq_true] at h
  obtain ⟨cg', hcg', htgt⟩ := h
  rw [List.any_eq_true] at htgt
  obtain ⟨m', hm', hres⟩ := htgt
  have hlt : m' < cg'.fns.length := List.mem_range.mp hm'
  exact ⟨cg', hcg', m', (resolvesTo_prop hres).1, hlt,
    (resolvesTo_prop hres).2.2⟩

/-- The per-signature existential pays `extSigResolves`. -/
theorem extSigResolves_of_prop {profile : String} {gs : List String}
    {e : ExtSig}
    (h : ∃ cg' ∈ clGroups profile gs, ∃ m' : Nat,
      e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
        ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧
          fn'.result = e.result) :
    extSigResolves (clGroups profile gs) e = true := by
  obtain ⟨cg', hcg', m', hr, hlt, fn', hget, hp, hres⟩ := h
  unfold extSigResolves
  rw [List.any_eq_true]
  exact ⟨cg', hcg', by
    rw [List.any_eq_true]
    exact ⟨m', List.mem_range.mpr hlt,
      resolvesTo_of_prop hr hlt hget hp hres⟩⟩

/-- `groupExtResolves` decided yields the `extResolves` conjunct for `cg`. -/
theorem groupExtResolves_prop {profile : String} {gs : List String}
    {cg : ClGroup}
    (h : groupExtResolves (clGroups profile gs) cg = true) :
    ∀ e ∈ cg.ext, ∃ cg' ∈ clGroups profile gs, ∃ m' : Nat,
      e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
        ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧
          fn'.result = e.result := by
  unfold groupExtResolves at h
  rw [List.all_eq_true] at h
  intro e he
  exact extSigResolves_prop (h e he)

/-- The `extResolves` conjunct pays `groupExtResolves` for `cg`. -/
theorem groupExtResolves_of_prop {profile : String} {gs : List String}
    {cg : ClGroup}
    (h : ∀ e ∈ cg.ext, ∃ cg' ∈ clGroups profile gs, ∃ m' : Nat,
      e.ref = encFnRef cg'.digest m' ∧ m' < cg'.fns.length ∧
        ∃ fn', cg'.fns.get? m' = some fn' ∧ fn'.params = e.params ∧
          fn'.result = e.result) :
    groupExtResolves (clGroups profile gs) cg = true := by
  unfold groupExtResolves
  rw [List.all_eq_true]
  intro e he
  exact extSigResolves_of_prop (h e he)

/-- The group-decode gate of `programAtClDec`, named to keep the match out
    of the outer `Bool` chain (the `programAtDecGroup` discipline). -/
def programAtClDecShape (profile : String) (cg : ClGroup) : Bool :=
  match (objSchema 19 profile).decode cg.bytes with
  | some (.group _ _ _) => true | _ => false

/-- The per-group conjunct of `programAtClDec`: kind-19 binding, `.group`
    decode, ext resolution into the bundle, digest reachable from `grp`,
    and the shared-catalog `elabBodies` at `F`. -/
def programAtClDecGroup (F : Int) (profile : String) (bcat grp : String)
    (cgs : List ClGroup) (cg : ClGroup) : Bool :=
  decide (CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, cg.digest⟩
      cg.bytes) &&
  programAtClDecShape profile cg &&
  groupExtResolves cgs cg &&
  decide (cg.digest ∈ closureSet cgs grp) &&
  (elabBodies (fuelN F)
    ⟨cg.fns.map (fun f => ⟨f.params, f.result⟩), cg.ext,
      catalogOf bcat⟩ cg.fns).toOption.isSome

/-- The entry conjunct: some bundle group's digest is the root's entry
    group, the member index is nonnegative and in range. -/
def programAtClDecEntry (cgs : List ClGroup) (grp : String) (m : Int) : Bool :=
  cgs.any fun cg =>
    (cg.digest == grp) && decide (0 ≤ m) && decide (m.toNat < cg.fns.length)

/-- The decidable reading of `ProgramAtAtCl` on raw ref/bytes inputs (the
    form-5 instrument): the two member bindings, the decoded root/bundle
    shapes with `broot` exactness, the catalog binding, non-empty
    duplicate-free groups, every group bound and `.group`-decoded, every
    ext signature resolved inside the bundle, the exact reachable digest
    set, the entry member in range, and per-group `elabBodies` at `F`. -/
def programAtClDec (F : Int) (profile : String) (rr : Ref) (rb : String)
    (br : Ref) (bb : String) : Bool :=
  decide (CanonicalObjectAt (objSchema 20 profile) rr rb) &&
  decide (CanonicalObjectAt (objSchema 21 "") br bb) &&
  match (objSchema 20 profile).decode rb, (objSchema 21 "").decode bb with
  | some (.root _ cat grp m), some (.bundle rb' bcat gs) =>
    (rb' == rb) &&
    decide (CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat) &&
    decide (gs ≠ [] ∧ gs.Nodup) &&
    (clGroups profile gs).all
      (programAtClDecGroup F profile bcat grp (clGroups profile gs)) &&
    programAtClDecEntry (clGroups profile gs) grp m
  | _, _ => false

/-- `programAtClDec` decided at the raw inputs yields the proposition. -/
theorem programAtAtCl_of_programAtClDec {F : Int} {profile : String}
    {rr : Ref} {rb : String} {br : Ref} {bb : String}
    (h : programAtClDec F profile rr rb br bb = true) :
    ∃ P : BoundCoreProgram profile,
      P.program_root_ref = rr ∧ P.program_root_bytes = rb ∧
      P.program_bundle_ref = br ∧ P.program_bundle_bytes = bb ∧
      ProgramAtAtCl F P := by
  unfold programAtClDec at h
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨hrootC, hbundleC⟩, hcl⟩ := h
  cases hrd : (objSchema 20 profile).decode rb with
  | none => rw [hrd] at hcl; dsimp only at hcl; cases hcl
  | some ro =>
    cases ro with
    | root pr cat grp m =>
      cases hbd : (objSchema 21 "").decode bb with
      | none => rw [hrd, hbd] at hcl; dsimp only at hcl; cases hcl
      | some bo =>
        cases bo with
        | bundle broot bcat gs =>
          rw [hrd, hbd] at hcl
          dsimp only at hcl
          rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
            Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hcl
          obtain ⟨⟨⟨⟨hrb, hcatC⟩, hN⟩, hgrps⟩, hent⟩ := hcl
          obtain ⟨hne, hnd⟩ := hN
          have hrb' : broot = rb := eq_of_beq hrb
          rw [List.all_eq_true] at hgrps
          refine ⟨⟨rr, rb, hrootC, br, bb, hbundleC,
              ⟨bcat, gs, hrb' ▸ hbd⟩⟩,
            rfl, rfl, rfl, rfl,
            ⟨pr, cat, grp, m, broot, bcat, gs, hrd, hbd, hcatC, hne, hnd,
              ?_, ?_, ?_, ?_, ?_⟩⟩
          · intro cg hcg
            have hg := hgrps cg hcg
            unfold programAtClDecGroup at hg
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg
            obtain ⟨⟨⟨⟨hcan, hshape⟩, _⟩, _⟩, _⟩ := hg
            refine ⟨hcan, ?_⟩
            unfold programAtClDecShape at hshape
            cases hdec : (objSchema 19 profile).decode cg.bytes with
            | none => rw [hdec] at hshape; cases hshape
            | some o =>
              cases o with
              | group prg' ext' fns' =>
                rw [hdec] at hshape
                obtain ⟨hp, he, hf⟩ := clGroups_fields hcg hdec
                rw [hp, he, hf]
              | _ => rw [hdec] at hshape; cases hshape
          · unfold programAtClDecEntry at hent
            rw [List.any_eq_true] at hent
            obtain ⟨cg, hcg, hent⟩ := hent
            rw [Bool.and_eq_true, Bool.and_eq_true] at hent
            obtain ⟨⟨hdg, he0⟩, hrange⟩ := hent
            exact ⟨cg, hcg, eq_of_beq hdg, of_decide_eq_true he0,
              of_decide_eq_true hrange⟩
          · intro cg hcg
            have hg := hgrps cg hcg
            unfold programAtClDecGroup at hg
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg
            obtain ⟨⟨⟨⟨_, _⟩, hres⟩, _⟩, _⟩ := hg
            intro e he
            exact groupExtResolves_prop hres e he
          · intro cg hcg
            have hg := hgrps cg hcg
            unfold programAtClDecGroup at hg
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hg
            obtain ⟨⟨⟨⟨_, _⟩, _⟩, hreach⟩, _⟩ := hg
            exact hreach
          · intro cg hcg
            have hg := hgrps cg hcg
            unfold programAtClDecGroup at hg
            rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
              Bool.and_eq_true] at hg
            exact hg.2
        | _ => rw [hrd, hbd] at hcl; dsimp only at hcl; cases hcl
    | _ => rw [hrd] at hcl; dsimp only at hcl; cases hcl

/-- The proposition decides `programAtClDec` on the program's own fields. -/
theorem programAtClDec_of_programAtAtCl {F : Int} {profile : String}
    {P : BoundCoreProgram profile} (h : ProgramAtAtCl F P) :
    programAtClDec F profile P.program_root_ref P.program_root_bytes
      P.program_bundle_ref P.program_bundle_bytes = true := by
  obtain ⟨pr, cat, grp, m, broot, bcat, gs, hrd, hbd, hc1, hne, hnd, hbind,
    hentry, hres, hreach, hbods⟩ := h
  unfold programAtClDec
  rw [decide_eq_true_eq.mpr P.program_root_at,
    decide_eq_true_eq.mpr P.program_bundle_at]
  rw [hrd, hbd]
  dsimp only
  obtain ⟨bcat', gs', hbd'⟩ := P.bundle_root_exact
  rw [hbd] at hbd'
  have h2 := Option.some.inj hbd'
  injection h2 with hb1 _ _
  subst hb1
  have hcatC' : decide (CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩
      bcat) = true := decide_eq_true_eq.mpr hc1
  have hN' : decide (gs ≠ [] ∧ gs.Nodup) = true :=
    decide_eq_true_eq.mpr ⟨hne, hnd⟩
  have hgrps : (clGroups profile gs).all (programAtClDecGroup F profile
      bcat grp (clGroups profile gs)) = true := by
    rw [List.all_eq_true]
    intro cg hcg
    obtain ⟨hcan, hdec⟩ := hbind cg hcg
    unfold programAtClDecGroup
    rw [decide_eq_true_eq.mpr hcan]
    unfold programAtClDecShape
    rw [hdec]
    dsimp only
    rw [groupExtResolves_of_prop (fun e he => hres cg hcg e he),
      decide_eq_true_eq.mpr (hreach cg hcg), hbods cg hcg]
    rfl
  have hent : programAtClDecEntry (clGroups profile gs) grp m = true := by
    unfold programAtClDecEntry
    rw [List.any_eq_true]
    obtain ⟨cg, hcg, hdg, he0, hrange⟩ := hentry
    refine ⟨cg, hcg, ?_⟩
    rw [beq_iff_eq.mpr hdg, decide_eq_true_eq.mpr he0,
      decide_eq_true_eq.mpr hrange]
    rfl
  rw [beq_iff_eq.mpr
    (rfl : P.program_root_bytes = P.program_root_bytes), hcatC', hN',
    hgrps, hent]
  rfl

/-! ## Agreement with the one-group `ProgramAtAt` -/

/-- Forward: a `ProgramAtAt` bundle is already the closure — `gs = [g]`,
    `ext = []`, so resolution is vacuous, the digest set is `{grp}`, and
    `progCheck`'s body check is the singleton's `elabBodies`. -/
theorem programAtAtCl_of_programAtAt {profile : String} {F : Int}
    {P : BoundCoreProgram profile} (h : ProgramAtAt F P) : ProgramAtAtCl F P := by
  obtain ⟨pr, cat, grp, m, broot, bcat, g, prg, ext, fns, hrd, hbd, hc1, hc2,
    hgd, hext, hentry, hck⟩ := h
  have hdg : dg g 19 = grp := hc2.2.1
  have hext0 : ext = [] := by simpa using hext
  subst hext0
  have hcg : clGroups profile [g] = [⟨g, dg g 19, prg, [], fns⟩] := by
    simp [clGroups, hgd]
  have hck' : ∃ out, progCheck F ⟨fns, [], catalogOf bcat, m⟩ = .ok out := by
    cases hp : progCheck F ⟨fns, [], catalogOf bcat, m⟩ with
    | error e => rw [hp] at hck; simp [Except.toOption] at hck
    | ok o' => exact ⟨o', rfl⟩
  obtain ⟨out, hpok⟩ := hck'
  obtain ⟨hcan, he0', ef, hef, hres, hb⟩ := progCheck_ok hpok
  have he0 : 0 ≤ m := he0'
  refine ⟨pr, cat, grp, m, broot, bcat, [g], hrd, hbd, hc1,
    by simp, by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro cg hcgm
    rw [hcg] at hcgm
    obtain rfl := List.mem_singleton.mp hcgm
    exact ⟨hdg ▸ hc2, hgd⟩
  · exact ⟨⟨g, dg g 19, prg, [], fns⟩, by rw [hcg]; simp, hdg, he0,
      by show m.toNat < fns.length; omega⟩
  · intro cg hcgm
    rw [hcg] at hcgm
    obtain rfl := List.mem_singleton.mp hcgm
    intro e he
    nomatch he
  · intro cg hcgm
    rw [hcg] at hcgm
    obtain rfl := List.mem_singleton.mp hcgm
    show dg g 19 ∈ closureSet (clGroups profile [g]) grp
    rw [hcg]
    have hcl : closureSet [⟨g, dg g 19, prg, [], fns⟩] grp = [grp] := by
      simp [closureSet, reachSteps, reachStep, extTargets, hdg]
    rw [hcl, hdg]
    simp
  · intro cg hcgm
    rw [hcg] at hcgm
    obtain rfl := List.mem_singleton.mp hcgm
    have hb' : elabBodies (fuelN F)
        ⟨fns.map (fun f => ⟨f.params, f.result⟩), [], catalogOf bcat⟩ fns =
        .ok out.1 := hb
    rw [hb']
    rfl

/-- Backward: on a one-group `ext = []` bundle the closure is exactly
    `ProgramAtAt` — resolution stays vacuous, the entry digest equality
    gives the group binding, and the singleton's `elabBodies` plus the
    catalog gate assemble `progCheck`. -/
theorem programAtAt_of_programAtAtCl {profile : String} {F : Int}
    {P : BoundCoreProgram profile}
    (hone : ∀ {gs broot bcat},
      (objSchema 21 "").decode P.program_bundle_bytes = some (.bundle broot bcat gs) →
      ∃ g prg ext fns, gs = [g] ∧ ext = [] ∧
        (objSchema 19 profile).decode g = some (.group prg ext fns))
    (h : ProgramAtAtCl F P) : ProgramAtAt F P := by
  obtain ⟨pr, cat, grp, m, broot, bcat, gs, hrd, hbd, hc1, hne, hnd, hbind,
    hentry, hres, hreach, hbods⟩ := h
  obtain ⟨g, prg, ext, fns, hgs, hext0, hgd⟩ := hone hbd
  subst hgs
  have hcg : clGroups profile [g] = [⟨g, dg g 19, prg, ext, fns⟩] := by
    simp [clGroups, hgd]
  have hbindg := hbind ⟨g, dg g 19, prg, ext, fns⟩ (by rw [hcg]; simp)
  have hdg : dg g 19 = grp := by
    obtain ⟨cg, hcgm, hcgd, _, _⟩ := hentry
    rw [hcg] at hcgm
    obtain rfl := List.mem_singleton.mp hcgm
    exact hcgd
  obtain ⟨cg, hcgm, hcgd, he0, hrange⟩ := hentry
  rw [hcg] at hcgm
  obtain rfl := List.mem_singleton.mp hcgm
  have hrange' : m.toNat < fns.length := hrange
  have hbindg' : CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, dg g 19⟩ g :=
    hbindg.1
  have hbod := hbods ⟨g, dg g 19, prg, ext, fns⟩ (by rw [hcg]; simp)
  have hbs : ∃ bs, elabBodies (fuelN F)
      ⟨fns.map (fun f => ⟨f.params, f.result⟩), ext, catalogOf bcat⟩ fns =
      .ok bs := by
    cases hb2 : elabBodies (fuelN F)
        ⟨fns.map (fun f => ⟨f.params, f.result⟩), ext, catalogOf bcat⟩ fns with
    | error e => rw [hb2] at hbod; simp [Except.toOption] at hbod
    | ok b' => exact ⟨b', rfl⟩
  obtain ⟨bs, hbs⟩ := hbs
  obtain ⟨ef, hef⟩ : ∃ ef, fns.get? m.toNat = some ef := by
    refine ⟨fns[m.toNat]'hrange', ?_⟩
    rw [List.get?_eq_getElem?]
    exact List.getElem?_eq_getElem hrange'
  subst hext0
  refine ⟨pr, cat, grp, m, broot, bcat, g, prg, [], fns, hrd, hbd, hc1, ?_,
    hgd, rfl, by omega, ?_⟩
  · exact hdg ▸ hbindg'
  · rw [progCheck_ok_of (catalogOf_canonical hc1) he0 hef hbs]
    rfl

/-- The agreement at the `∃ F` level. -/
theorem programAtCl_of_programAt {profile : String} {P : BoundCoreProgram profile}
    (h : ProgramAt P) : ProgramAtCl P := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, programAtAtCl_of_programAtAt hF⟩

theorem programAt_of_programAtCl {profile : String} {P : BoundCoreProgram profile}
    (hone : ∀ {gs broot bcat},
      (objSchema 21 "").decode P.program_bundle_bytes = some (.bundle broot bcat gs) →
      ∃ g prg ext fns, gs = [g] ∧ ext = [] ∧
        (objSchema 19 profile).decode g = some (.group prg ext fns))
    (h : ProgramAtCl P) : ProgramAt P := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, programAtAt_of_programAtAtCl hone hF⟩

end Rcic.Scm.BoundProgAt
