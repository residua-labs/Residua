/-
M1 — 06 §18 `BoundCoreProgram` and `ProgramAt`/`ProgramBundleAt` as R-CIC
propositions over bound references and canonical bytes (docs/rcic/
06_SCM_CORE_SEMANTICS.md §18 "Bound objects", fields at :372–:388),
pinned to the K3b carrier `apps/rcic-scm-bound-program`
(`lean/rcic/ScmBoundProgram.lean`, `scmBP` form 3 = `bpProgram`).

Following the K3c snapshot's convention (`ScmBoundCoreTV.lean`), every
decode in the propositions is at the input's own fuel (`b.length`, the
convention `objSchema.decode` already uses); agreement with the carrier is
stated at each member's own fuel.  Carrier acceptance at an arbitrary fuel
implies the propositions only modulo the decoder's fuel monotonicity — a
K3c lemma recorded as debt, not assumed here.  The `progCheck` closure
condition is an `∃` over fuel because the carrier's elaboration budget is
not a property of the bytes.

[spec_ambiguity] 06 §18 names `ProgramAt` without giving its signature.
`ScmEmbed.lean:26–27` records `program_bundle_at` as the working reading:
the form-3 bound program (root + bundle with exact closure), existentially
quantified over the program-check fuel.  `ProgramBundleAt` is the census
row's name for the same proposition.

[spec_tree_conflict] `ScmRawRelations.lean:17–26` still lists the bound
objects as not transcribed; the type/value half is transcribed in
`ScmBoundCoreTV.lean` (#6064) and this file covers the program half.

The `∀`-level propositions cannot be inhabited on concrete bytes in the
kernel (the decoder is extern-backed — M-005), so all pins below are
native `#guard`s, and every ∃-predicate carries a `programAtDec`-level
refusal tooth beside its accepting pins plus a theorem-level refusal
lemma under decoded-shape hypotheses.
-/

import rcic.ScmBoundProgram

namespace Rcic.Scm.BoundProgAt
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject Rcic.Scm.BoundProg

/-! ## The residue catalog a bundle member decodes to -/

/-- The Prop-side reading of `objCatalog`: the entries of the bundle's
    catalog member under the schema's own decode, `[]` when absent. -/
def catalogOf (bcat : String) : List CatalogEntry :=
  match (objSchema 18 "").decode bcat with
  | some (.catalog c) => c
  | _ => []

/-! ## 06 §18 `BoundCoreProgram` — the seven fields verbatim -/

/-- 06 §18 `BoundCoreProgram`: a program root object and a program bundle
    object, each bound (01 §6 `CanonicalObjectAt`) at its canonical bytes,
    with the bundle's stored root-bytes field exactly the program root's
    bytes (`bundle_root_exact`). -/
structure BoundCoreProgram (profile : String) where
  program_root_ref : Ref
  program_root_bytes : String
  program_root_at : CanonicalObjectAt (objSchema 20 profile)
    program_root_ref program_root_bytes
  program_bundle_ref : Ref
  program_bundle_bytes : String
  program_bundle_at : CanonicalObjectAt (objSchema 21 "")
    program_bundle_ref program_bundle_bytes
  bundle_root_exact : ∃ bcat gs,
    (objSchema 21 "").decode program_bundle_bytes =
      some (.bundle program_root_bytes bcat gs)

/-- The program the bound objects assemble: the entry member's function
    list, the bundle's catalog, the root's member index — the same
    `RawProg` the carrier's `bpProgram` reports in `.bound`. -/
def BoundCoreProgram.prog {profile : String} (P : BoundCoreProgram profile) : RawProg :=
  match (objSchema 20 profile).decode P.program_root_bytes with
  | some (.root _ _ _ m) =>
    match (objSchema 21 "").decode P.program_bundle_bytes with
    | some (.bundle _ bcat gs) =>
      (match (objSchema 19 profile).decode (gs.headD "") with
       | some (.group _ _ fns) => ⟨fns, [], catalogOf bcat, m⟩
       | _ => ⟨[], [], catalogOf bcat, m⟩)
    | _ => ⟨[], [], [], 0⟩
  | _ => ⟨[], [], [], 0⟩

/-! ## `ProgramAtAt`/`ProgramAt` — the form-3 closure as a proposition -/

/-- The form-3 closure at program-check fuel `F`, in the K3c snapshot's
    ∃-decode style (`ValueAt`): the root decodes to a program root, the
    bundle to a one-group bundle over the root's bytes (exactness itself
    is `P.bundle_root_exact`), the catalog the root names binds
    canonically, the group the root names binds under the profile, the
    group has no external signatures, the entry member is in range, and
    the assembled program passes `progCheck` at `F`. -/
def ProgramAtAt {profile : String} (F : Int) (P : BoundCoreProgram profile) : Prop :=
  ∃ pr cat grp m broot bcat g prg ext fns,
    (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m) ∧
    (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]) ∧
    CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat ∧
    CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, grp⟩ g ∧
    (objSchema 19 profile).decode g = some (.group prg ext fns) ∧
    ext.length = 0 ∧ m < fns.length ∧
    (progCheck F ⟨fns, [], catalogOf bcat, m⟩).toOption.isSome = true

/-- 06 §18 `ProgramAt`, read as `program_bundle_at` ([spec_ambiguity] —
    §18 gives no signature): the program's one-group bound closure holds
    at some program-check fuel. -/
def ProgramAt {profile : String} (P : BoundCoreProgram profile) : Prop :=
  ∃ F : Int, ProgramAtAt F P

/-- The census row's name (`ProgramBundleAt binds exact closure`,
    00_ANNEX_24 SCM-015) for `ProgramAt`. -/
abbrev ProgramBundleAt {profile : String} (P : BoundCoreProgram profile) : Prop :=
  ProgramAt P

/-- The group-closure conjunct of `programAtDec`, lifted to a named def:
    inlined in the outer match the compiler leaks a kernel variable
    (`_kernel_fresh`) when `decide` over `CanonicalObjectAt` mixes with
    the nested group match. -/
def programAtDecGroup (F : Int) (profile : String)
    (m : Int) (bcat g : String) : Bool :=
  match (objSchema 19 profile).decode g with
  | some (.group _ ext fns) =>
    (ext.length == 0) && decide (m < fns.length) &&
      (progCheck F ⟨fns, [], catalogOf bcat, m⟩).toOption.isSome
  | _ => false

/-- The decidable reading of `ProgramAtAt` on raw ref/bytes inputs (the
    pin instrument): the two member bindings, the decoded form-3 shapes,
    the catalog and group bindings the root names, the one-group closure,
    the no-external-signatures and entry-range conditions, and `progCheck`
    at `F`. -/
def programAtDec (F : Int) (profile : String) (rr : Ref) (rb : String)
    (br : Ref) (bb : String) : Bool :=
  decide (CanonicalObjectAt (objSchema 20 profile) rr rb) &&
  decide (CanonicalObjectAt (objSchema 21 "") br bb) &&
  match (objSchema 20 profile).decode rb, (objSchema 21 "").decode bb with
  | some (.root _ cat grp m), some (.bundle rb' bcat [g]) =>
    (rb' == rb) &&
    decide (CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat) &&
    decide (CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, grp⟩ g) &&
    programAtDecGroup F profile m bcat g
  | _, _ => false

/-! ## `objSchema.decode` is the own-fuel `objDec` (modulo the §6 order gate) -/

/-- `objSchema.decode` reads the own-fuel `objDec`; for a catalog the §6
    canonical order is additionally required (the gate `bpCatalog`
    decides). -/
theorem objSchema_decode_eq {kind : Int} {profile : String} {b : String}
    {o : Obj} {p : Nat}
    (hd : objDec b.length kind b = .ok (o, p))
    (hord : kind = 18 → catalogCanonical (objCatalog o) = true) :
    (objSchema kind profile).decode b = some o := by
  show (match objDec b.length kind b with
        | .ok (o', _) =>
          if kind = 18 ∧ !catalogCanonical (objCatalog o') then none else some o'
        | .error _ => none) = some o
  rw [hd]
  have hne : ¬ (kind = 18 ∧ !catalogCanonical (objCatalog o)) := by
    rintro ⟨h18, hnc⟩
    rw [hord h18] at hnc
    exact absurd hnc (by decide)
  show (if kind = 18 ∧ !catalogCanonical (objCatalog o) then none
        else some o) = some o
  rw [if_neg hne]

/-- Every accepting `objDec` result comes through `objOf` — the
    constructor the kind dispatches to. -/
theorem objDec_shape {F kind : Int} {b : String} {o : Obj} {p : Nat}
    (h : objDec F kind b = .ok (o, p)) (hk : kind ≤ 21) :
    ∃ xs, o = objOf kind xs := by
  unfold objDec at h
  rw [if_neg (by omega : ¬ kind > 21)] at h
  dsimp only at h
  cases hc : charAt b.toList.toArray 0 with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    dsimp only at h
    by_cases ht : c ≠ kindTag kind
    · rw [if_pos ht] at h; cases h
    · rw [if_neg ht] at h
      cases hd : decSeq b.toList.toArray (gasFor F b.toList.toArray.size) F 1
          (kindSeq kind) with
      | error e => rw [hd] at h; cases h
      | ok v =>
        obtain ⟨xs, q⟩ := v
        rw [hd] at h
        cases h
        exact ⟨xs, rfl⟩

theorem objDec_catalog {F : Int} {b : String} {o : Obj} {p : Nat}
    (h : objDec F 18 b = .ok (o, p)) : ∃ c, o = .catalog c := by
  obtain ⟨xs, rfl⟩ := objDec_shape h (by decide)
  exact ⟨_, rfl⟩

theorem objDec_group {F : Int} {b : String} {o : Obj} {p : Nat}
    (h : objDec F 19 b = .ok (o, p)) : ∃ pr ext fns, o = .group pr ext fns := by
  obtain ⟨xs, rfl⟩ := objDec_shape h (by decide)
  exact ⟨_, _, _, rfl⟩

theorem objDec_root {F : Int} {b : String} {o : Obj} {p : Nat}
    (h : objDec F 20 b = .ok (o, p)) : ∃ pr cat grp m, o = .root pr cat grp m := by
  obtain ⟨xs, rfl⟩ := objDec_shape h (by decide)
  exact ⟨_, _, _, _, rfl⟩

theorem objDec_bundle {F : Int} {b : String} {o : Obj} {p : Nat}
    (h : objDec F 21 b = .ok (o, p)) : ∃ rb bcat gs, o = .bundle rb bcat gs := by
  obtain ⟨xs, rfl⟩ := objDec_shape h (by decide)
  exact ⟨_, _, _, rfl⟩

/-! ## Member acceptance at own fuel establishes `CanonicalObjectAt` -/

theorem objBind_x_of_accepts {F : Int} {r : Ref} {kind : Int} {b : String}
    {o : Obj} {p : Nat}
    (h : (objBind F r kind b).ok = 1) (hd : objDec F kind b = .ok (o, p)) :
    (objBind F r kind b).x = o := by
  obtain ⟨hcls, hkind, ⟨o', p', hd', hp', henc⟩, hdig⟩ := objBind_accepts _ _ _ _ h
  rw [hd] at hd'
  cases hd'
  unfold objBind
  rw [if_neg (not_not_intro hcls), if_neg (not_not_intro hkind), hd]
  dsimp only
  rw [if_neg (not_not_intro hp'), if_neg (not_not_intro henc),
    if_neg (not_not_intro hdig)]
  rfl

/-- An accepting `bpMember` unpacks to the object binding plus the decoded
    object's profile. -/
theorem bpMember_accepts {F : Int} {profile : String} {r : Ref} {kind : Int}
    {b : String} (h : (bpMember F profile r kind b).ok = 1) :
    (objBind F r kind b).ok = 1 ∧ objProfile (objBind F r kind b).x = profile := by
  unfold bpMember at h
  dsimp only at h
  by_cases hz : (objBind F r kind b).ok = 0
  · rw [if_pos hz] at h
    rw [hz] at h
    exact absurd h (by decide)
  · rw [if_neg hz] at h
    by_cases hp : objProfile (objBind F r kind b).x = profile
    · rw [if_pos hp] at h
      exact ⟨h, hp⟩
    · rw [if_neg hp] at h
      have h0 : (0 : Int) = 1 := h
      exact absurd h0 (by decide)

/-- An accepting `bpCatalog` unpacks to the object binding plus the §6
    canonical order on the decoded catalog. -/
theorem bpCatalog_accepts {F : Int} {r : Ref} {b : String}
    (h : (bpCatalog F r b).ok = 1) :
    (objBind F r 18 b).ok = 1 ∧
      catalogCanonical (objCatalog (objBind F r 18 b).x) = true := by
  unfold bpCatalog at h
  dsimp only at h
  by_cases hz : (objBind F r 18 b).ok = 0
  · rw [if_pos hz] at h
    rw [hz] at h
    exact absurd h (by decide)
  · rw [if_neg hz] at h
    by_cases hc : catalogCanonical (objCatalog (objBind F r 18 b).x)
    · rw [if_pos hc] at h
      exact ⟨h, hc⟩
    · rw [if_neg hc] at h
      have h0 : (0 : Int) = 1 := h
      exact absurd h0 (by decide)

/-- `bpMember` accepting returns its `objBind` result object. -/
theorem bpMember_x_of_accepts {F : Int} {profile : String} {r : Ref} {kind : Int}
    {b : String} (h : (bpMember F profile r kind b).ok = 1) :
    (bpMember F profile r kind b).x = (objBind F r kind b).x := by
  obtain ⟨hb, hpr⟩ := bpMember_accepts h
  unfold bpMember
  dsimp only
  rw [if_neg (by intro hz; rw [hz] at hb; exact absurd hb (by decide)),
    if_pos hpr]

/-- `bpCatalog` accepting returns its `objBind` result object. -/
theorem bpCatalog_x_of_accepts {F : Int} {r : Ref} {b : String}
    (h : (bpCatalog F r b).ok = 1) :
    (bpCatalog F r b).x = (objBind F r 18 b).x := by
  obtain ⟨hb, hc⟩ := bpCatalog_accepts h
  unfold bpCatalog
  dsimp only
  rw [if_neg (by intro hz; rw [hz] at hb; exact absurd hb (by decide)),
    if_pos hc]

/-- The generic conversion: an `objBind` acceptance at the input's own
    fuel plus the schema's per-object side conditions establishes 01 §6
    `CanonicalObjectAt`. -/
theorem canonicalObjectAt_of_objBind {profile : String} {r : Ref} {kind : Int}
    {b : String}
    (h : (objBind b.length r kind b).ok = 1)
    (hschema : ∀ o, objDec b.length kind b = .ok (o, b.length) →
      (kind = 18 → catalogCanonical (objCatalog o) = true) ∧
      (objProfile o = profile ∨ kind = 18)) :
    CanonicalObjectAt (objSchema kind profile) r b := by
  obtain ⟨hcls, hkind, ⟨o, p, hd, hp, henc⟩, hdig⟩ := objBind_accepts _ _ _ _ h
  subst hp
  obtain ⟨hord, hprof⟩ := hschema o hd
  have hdec : (objSchema kind profile).decode b = some o :=
    objSchema_decode_eq hd hord
  unfold CanonicalObjectAt
  rw [hdec]
  refine ⟨⟨henc, ?_⟩, ?_, ?_⟩
  · show (r.cls == 3 && r.kind == kind && (kind == 18 || objProfile o == profile)) = true
    rw [hcls, hkind]
    cases hprof with
    | inl hpr => rw [hpr]; simp
    | inr h18 => rw [h18]; rfl
  · rw [hcls, hkind]
    exact hdig
  · show (match objDec b.length kind b with
          | .ok (_, p') => p' == b.length
          | .error _ => false) = true
    rw [hd]
    exact beq_self_eq_true _

/-- A group or root bound under `profile` at its own fuel is a
    `CanonicalObjectAt` at that profile's schema. -/
theorem canonicalObjectAt_of_bpMember {profile : String} {r : Ref} {kind : Int}
    {b : String}
    (h : (bpMember b.length profile r kind b).ok = 1)
    (horder : kind = 18 → ∀ o, objDec b.length kind b = .ok (o, b.length) →
      catalogCanonical (objCatalog o) = true) :
    CanonicalObjectAt (objSchema kind profile) r b := by
  obtain ⟨hb, hpr⟩ := bpMember_accepts h
  exact canonicalObjectAt_of_objBind hb (fun o hd => by
    refine ⟨fun h18 => horder h18 o hd, .inl ?_⟩
    have hx := objBind_x_of_accepts hb hd
    rw [hx] at hpr
    exact hpr)

/-- A catalog bound in §6 order at its own fuel is a `CanonicalObjectAt`
    (the kind-18 schema carries no profile). -/
theorem canonicalObjectAt_of_bpCatalog {r : Ref} {b : String}
    (h : (bpCatalog b.length r b).ok = 1) :
    CanonicalObjectAt (objSchema 18 "") r b := by
  obtain ⟨hb, hc⟩ := bpCatalog_accepts h
  obtain ⟨_, _, ⟨o, p, hd, hp, _⟩, _⟩ := objBind_accepts _ _ _ _ hb
  subst hp
  have hx := objBind_x_of_accepts hb hd
  rw [hx] at hc
  exact canonicalObjectAt_of_objBind hb (fun o' hd' => by
    rw [hd] at hd'
    cases hd'
    exact ⟨fun _ => hc, .inr rfl⟩)

/-- A kind-21 object bound at its own fuel is a `CanonicalObjectAt` at the
    bundle schema (a bundle carries no profile). -/
theorem canonicalObjectAt_of_objBind21 {r : Ref} {b : String}
    (h : (objBind b.length r 21 b).ok = 1) :
    CanonicalObjectAt (objSchema 21 "") r b := by
  exact canonicalObjectAt_of_objBind h (fun o hd => by
    obtain ⟨xs, rfl⟩ := objDec_shape hd (by decide)
    exact ⟨fun h18 => absurd h18 (by decide), .inl rfl⟩)

/-- `catalogOf` reads the catalog member the schema decodes. -/
theorem catalogOf_eq {bcat : String} {c : List CatalogEntry}
    (h : (objSchema 18 "").decode bcat = some (.catalog c)) :
    catalogOf bcat = c := by
  show (match (objSchema 18 "").decode bcat with
        | some (.catalog c') => c'
        | _ => []) = c
  rw [h]

/-! ## What `bpProgram` acceptance establishes -/

theorem objBind_ok01 {F : Int} {r : Ref} {kind : Int} {b : String} :
    (objBind F r kind b).ok = 0 ∨ (objBind F r kind b).ok = 1 := by
  unfold objBind
  by_cases h1 : r.cls ≠ 3
  · rw [if_pos h1]; exact Or.inl rfl
  · rw [if_neg h1]
    by_cases h2 : r.kind ≠ kind
    · rw [if_pos h2]; exact Or.inl rfl
    · rw [if_neg h2]
      cases hd : objDec F kind b with
      | error c => exact Or.inl rfl
      | ok v =>
        obtain ⟨o, p⟩ := v
        dsimp only
        by_cases h3 : p ≠ b.length
        · rw [if_pos h3]; exact Or.inl rfl
        · rw [if_neg h3]
          by_cases h4 : objEnc o ≠ b
          · rw [if_pos h4]; exact Or.inl rfl
          · rw [if_neg h4]
            by_cases h5 : Rcic.TypedRef.deriveDigest 3 kind b ≠ r.digest
            · rw [if_pos h5]; exact Or.inl rfl
            · rw [if_neg h5]; exact Or.inr rfl

theorem bpMember_ok01 {F : Int} {profile : String} {r : Ref} {kind : Int}
    {b : String} :
    (bpMember F profile r kind b).ok = 0 ∨ (bpMember F profile r kind b).ok = 1 := by
  unfold bpMember
  dsimp only
  by_cases hz : (objBind F r kind b).ok = 0
  · rw [if_pos hz]; exact Or.inl hz
  · rw [if_neg hz]
    by_cases hp : objProfile (objBind F r kind b).x = profile
    · rw [if_pos hp]; exact objBind_ok01
    · rw [if_neg hp]; exact Or.inl rfl

theorem bpCatalog_ok01 {F : Int} {r : Ref} {b : String} :
    (bpCatalog F r b).ok = 0 ∨ (bpCatalog F r b).ok = 1 := by
  unfold bpCatalog
  dsimp only
  by_cases hz : (objBind F r 18 b).ok = 0
  · rw [if_pos hz]; exact Or.inl hz
  · rw [if_neg hz]
    cases hc : catalogCanonical (objCatalog (objBind F r 18 b).x) with
    | false => exact Or.inl rfl
    | true => exact objBind_ok01

/-- The composed form-3 acceptance unpacks to: the root bound under the
    profile, the bundle bound with the root's bytes and exactly one group,
    the catalog and group the root names bound, no external signatures,
    the entry member in range, and the program typing at `F`. -/
theorem bpProgram_accepts {F : Int} {profile : String} {rr : Ref} {rb : String}
    {br : Ref} {bb : String} (h : (bpProgram F profile rr rb br bb).ok = 1) :
    ∃ cat grp m bcat g cobj ext fns,
      objDec F 20 rb = .ok (.root profile cat grp m, rb.length) ∧
      objDec F 21 bb = .ok (.bundle rb bcat [g], bb.length) ∧
      objDec F 18 bcat = .ok (.catalog cobj, bcat.length) ∧
      catalogCanonical cobj = true ∧
      objDec F 19 g = .ok (.group profile ext fns, g.length) ∧
      ext.length = 0 ∧ m < fns.length ∧
      ∃ out, progCheck F ⟨fns, [], cobj, m⟩ = .ok out := by
  unfold bpProgram at h
  dsimp only at h
  by_cases hz : (bpMember F profile rr 20 rb).ok = 0
  · rw [if_pos hz] at h
    rw [hz] at h
    exact absurd h (by decide)
  rw [if_neg hz] at h
  have hr1 : (bpMember F profile rr 20 rb).ok = 1 := by
    cases bpMember_ok01 with
    | inl h0 => exact absurd h0 hz
    | inr h1 => exact h1
  obtain ⟨hrootB, hrootP⟩ := bpMember_accepts hr1
  by_cases hbz : (objBind F br 21 bb).ok = 0
  · rw [if_pos hbz] at h
    rw [hbz] at h
    exact absurd h (by decide)
  rw [if_neg hbz] at h
  have hb1 : (objBind F br 21 bb).ok = 1 := by
    cases objBind_ok01 with
    | inl h0 => exact absurd h0 hbz
    | inr h1 => exact h1
  obtain ⟨_, _, ⟨ro, rp, hrd, hrp, _⟩, _⟩ := objBind_accepts _ _ _ _ hrootB
  subst hrp
  obtain ⟨pr, cat, grp, m, hrootO⟩ := objDec_root hrd
  subst hrootO
  have hpr : pr = profile := by
    have hx := objBind_x_of_accepts hrootB hrd
    rw [hx] at hrootP
    exact hrootP
  subst pr
  obtain ⟨_, _, ⟨bo, bp, hbd, hbp, _⟩, _⟩ := objBind_accepts _ _ _ _ hb1
  subst hbp
  obtain ⟨broot, bcat, gs, hbo⟩ := objDec_bundle hbd
  subst hbo
  have hxr : (bpMember F profile rr 20 rb).x = .root profile cat grp m := by
    rw [bpMember_x_of_accepts hr1, objBind_x_of_accepts hrootB hrd]
  have hxb : (objBind F br 21 bb).x = .bundle broot bcat gs :=
    objBind_x_of_accepts hb1 hbd
  rw [hxr, hxb] at h
  dsimp only at h
  by_cases hx : broot ≠ rb
  · rw [if_pos hx] at h
    have h0 : (0 : Int) = 1 := h
    exact absurd h0 (by decide)
  rw [if_neg hx] at h
  have hbr : broot = rb := Decidable.of_not_not hx
  rw [hbr] at hbd
  by_cases hcz : (bpCatalog F ⟨3, 18, cat⟩ bcat).ok = 0
  · rw [if_pos hcz] at h
    rw [hcz] at h
    exact absurd h (by decide)
  rw [if_neg hcz] at h
  have hc1 : (bpCatalog F ⟨3, 18, cat⟩ bcat).ok = 1 := by
    cases bpCatalog_ok01 with
    | inl h0 => exact absurd h0 hcz
    | inr h1 => exact h1
  obtain ⟨hcatB, hcatC⟩ := bpCatalog_accepts hc1
  obtain ⟨_, _, ⟨co, cp, hcd, hcp, _⟩, _⟩ := objBind_accepts _ _ _ _ hcatB
  subst hcp
  obtain ⟨cobj, hco⟩ := objDec_catalog hcd
  subst hco
  have hcan : catalogCanonical cobj = true := by
    have hx2 := objBind_x_of_accepts hcatB hcd
    rw [hx2] at hcatC
    exact hcatC
  by_cases hgs : gs.length ≠ 1
  · rw [if_pos hgs] at h
    have h0 : (0 : Int) = 1 := h
    exact absurd h0 (by decide)
  rw [if_neg hgs] at h
  obtain ⟨g, hgs1⟩ := List.length_eq_one.mp (Decidable.of_not_not hgs)
  subst hgs1
  simp only [List.headD] at h
  by_cases hgz : (bpMember F profile ⟨3, 19, grp⟩ 19 g).ok = 0
  · rw [if_pos hgz] at h
    rw [hgz] at h
    exact absurd h (by decide)
  rw [if_neg hgz] at h
  have hg1b : (bpMember F profile ⟨3, 19, grp⟩ 19 g).ok = 1 := by
    cases bpMember_ok01 with
    | inl h0 => exact absurd h0 hgz
    | inr h1 => exact h1
  obtain ⟨hgrpB, hgrpP⟩ := bpMember_accepts hg1b
  obtain ⟨_, _, ⟨go, gp, hgd, hgp, _⟩, _⟩ := objBind_accepts _ _ _ _ hgrpB
  subst hgp
  obtain ⟨prg, ext, fns, hgo⟩ := objDec_group hgd
  subst hgo
  have hprg : prg = profile := by
    have hx := objBind_x_of_accepts hgrpB hgd
    rw [hx] at hgrpP
    exact hgrpP
  subst prg
  have hxg : (bpMember F profile ⟨3, 19, grp⟩ 19 g).x = .group profile ext fns := by
    rw [bpMember_x_of_accepts hg1b, objBind_x_of_accepts hgrpB hgd]
  rw [hxg] at h
  dsimp only at h
  by_cases hex : ext.length ≠ 0
  · rw [if_pos hex] at h
    have h0 : (0 : Int) = 1 := h
    exact absurd h0 (by decide)
  rw [if_neg hex] at h
  have hext : ext.length = 0 := Decidable.of_not_not hex
  by_cases hent : ¬ (m < fns.length)
  · rw [if_pos hent] at h
    have h0 : (0 : Int) = 1 := h
    exact absurd h0 (by decide)
  rw [if_neg hent] at h
  have hentry : m < fns.length := Decidable.of_not_not hent
  have hcx : (bpCatalog F ⟨3, 18, cat⟩ bcat).x = .catalog cobj := by
    rw [bpCatalog_x_of_accepts hc1, objBind_x_of_accepts hcatB hcd]
  have hcat' : objCatalog (bpCatalog F ⟨3, 18, cat⟩ bcat).x = cobj := by
    rw [hcx]
    rfl
  rw [hcat'] at h
  cases hpc : progCheck F ⟨fns, [], cobj, m⟩ with
  | error e =>
    rw [hpc] at h
    dsimp only at h
    have h0 : (0 : Int) = 1 := h
    exact absurd h0 (by decide)
  | ok out =>
    exact ⟨cat, grp, m, bcat, g, cobj, ext, fns, hrd, hbd, hcd, hcan, hgd,
      hext, hentry, out, hpc⟩

/-! ## `progCheck` unpacking -/

theorem progCheck_ok {F : Int} {p : RawProg}
    {out : Σ' (_ : Bodies (sigOf p) (sigOf p).fns), CoreTy}
    (h : progCheck F p = .ok out) :
    catalogCanonical p.catalog = true ∧ 0 ≤ p.entry ∧
    ∃ ef, p.fns.get? p.entry.toNat = some ef ∧ out.2 = ef.result ∧
      elabBodies (fuelN F) (sigOf p) p.fns = .ok out.1 := by
  unfold progCheck at h
  by_cases hc : !catalogCanonical p.catalog
  · rw [if_pos hc] at h
    cases h
  rw [if_neg hc] at h
  have hcan : catalogCanonical p.catalog = true := by
    cases hc2 : catalogCanonical p.catalog with
    | true => rfl
    | false => rw [hc2] at hc; exact absurd hc (by decide)
  by_cases he : p.entry < 0
  · rw [if_pos he] at h
    cases h
  rw [if_neg he] at h
  cases hg : p.fns.get? p.entry.toNat with
  | none =>
    rw [hg] at h
    cases h
  | some ef =>
    rw [hg] at h
    dsimp only at h
    cases hb : elabBodies (fuelN F) (sigOf p) p.fns with
    | error e =>
      rw [hb] at h
      cases h
    | ok bs =>
      rw [hb] at h
      cases h
      exact ⟨hcan, by omega, ef, rfl, rfl, rfl⟩

theorem progCheck_isOk_entry {F : Int} {p : RawProg}
    (h : (progCheck F p).toOption.isSome = true) : 0 ≤ p.entry := by
  cases hpc : progCheck F p with
  | error e =>
    rw [hpc] at h
    simp [Except.toOption] at h
  | ok out =>
    obtain ⟨_, he, _⟩ := progCheck_ok hpc
    exact he

/-! ## Building the proposition: own-fuel component acceptance -/

/-- The own-fuel agreement for form 3: each member binding accepted at its
    input's own fuel, the decoded shapes the carrier's `bpProgram` checks,
    and `progCheck` at `F` give a `BoundCoreProgram` satisfying
    `ProgramAtAt F`.  (`bpProgram` at its own fuel F supplies the same
    decoded shapes; the pins exercise both at the corpus rows.) -/
theorem programAtAt_of_ownFuel {profile : String} {F : Int}
    {rr : Ref} {rb : String} {br : Ref} {bb : String}
    (hroot : (bpMember rb.length profile rr 20 rb).ok = 1)
    (hbundle : (objBind bb.length br 21 bb).ok = 1)
    {pr cat grp : String} {m : Int} {bcat g : String}
    (hrd : (objSchema 20 profile).decode rb = some (.root pr cat grp m))
    (hbd : (objSchema 21 "").decode bb = some (.bundle rb bcat [g]))
    (hcat : (bpCatalog bcat.length ⟨3, 18, cat⟩ bcat).ok = 1)
    (hgroup : (bpMember g.length profile ⟨3, 19, grp⟩ 19 g).ok = 1)
    {prg : String} {ext : List ExtSig} {fns : List RawFnDef}
    (hgd : (objSchema 19 profile).decode g = some (.group prg ext fns))
    (hext : ext.length = 0)
    (hentry : m < fns.length)
    (hcheck : (progCheck F ⟨fns, [], catalogOf bcat, m⟩).toOption.isSome = true) :
    ∃ P : BoundCoreProgram profile, ProgramAtAt F P := by
  refine ⟨⟨rr, rb,
      canonicalObjectAt_of_bpMember (kind := 20) hroot
        (fun h18 => absurd h18 (by decide)),
      br, bb, canonicalObjectAt_of_objBind21 hbundle, ⟨bcat, [g], hbd⟩⟩,
    pr, cat, grp, m, rb, bcat, g, prg, ext, fns, hrd, hbd,
    canonicalObjectAt_of_bpCatalog hcat,
    canonicalObjectAt_of_bpMember (kind := 19) hgroup
      (fun h18 => absurd h18 (by decide)),
    hgd, hext, hentry, hcheck⟩

/-- `programAtDec` decided at the raw inputs yields the proposition: the
    pin instrument agrees with the Prop, not just with the carrier. -/
theorem programAtAt_of_programAtDec {F : Int} {profile : String}
    {rr : Ref} {rb : String} {br : Ref} {bb : String}
    (h : programAtDec F profile rr rb br bb = true) :
    ∃ P : BoundCoreProgram profile,
      P.program_root_ref = rr ∧ P.program_root_bytes = rb ∧
      P.program_bundle_ref = br ∧ P.program_bundle_bytes = bb ∧
      ProgramAtAt F P := by
  unfold programAtDec at h
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
          cases gs with
          | nil => rw [hrd, hbd] at hcl; dsimp only at hcl; cases hcl
          | cons g tail =>
            cases tail with
            | nil =>
              rw [hrd, hbd] at hcl
              dsimp only at hcl
              rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
                decide_eq_true_eq, decide_eq_true_eq] at hcl
              obtain ⟨⟨⟨hrb, hcatC⟩, hgrpC⟩, hgC⟩ := hcl
              have hrb' : broot = rb := eq_of_beq hrb
              rw [hrb'] at hbd
              generalize hgd : (objSchema 19 profile).decode g = dg
              cases dg with
              | none =>
                unfold programAtDecGroup at hgC
                rw [hgd] at hgC; dsimp only at hgC; cases hgC
              | some go =>
                cases go with
                | group prg ext fns =>
                  unfold programAtDecGroup at hgC
                  rw [hgd] at hgC
                  dsimp only at hgC
                  rw [Bool.and_eq_true, Bool.and_eq_true,
                    decide_eq_true_eq] at hgC
                  obtain ⟨⟨hlen, hent⟩, hck⟩ := hgC
                  have hext : ext.length = 0 := eq_of_beq hlen
                  exact ⟨⟨rr, rb, hrootC, br, bb, hbundleC,
                      ⟨bcat, [g], hbd⟩⟩,
                    rfl, rfl, rfl, rfl,
                    ⟨pr, cat, grp, m, rb, bcat, g, prg, ext, fns,
                      hrd, hbd, hcatC, hgrpC, hgd, hext, hent, hck⟩⟩
                | _ =>
                  unfold programAtDecGroup at hgC
                  rw [hgd] at hgC; dsimp only at hgC; cases hgC
            | cons _ _ => rw [hrd, hbd] at hcl; dsimp only at hcl; cases hcl
        | _ => rw [hrd, hbd] at hcl; dsimp only at hcl; cases hcl
    | _ => rw [hrd] at hcl; dsimp only at hcl; cases hcl

/-- What `ProgramAtAt` establishes (the eliminator the teeth and the
    bridge halves consume) — the ∃-form is already the decomposed
    reading; this alias keeps the seal name. -/
theorem programAtAt_decompose {profile : String} {F : Int}
    {P : BoundCoreProgram profile} (h : ProgramAtAt F P) :
    ∃ pr cat grp m broot bcat g prg ext fns,
      (objSchema 20 profile).decode P.program_root_bytes =
        some (.root pr cat grp m) ∧
      (objSchema 21 "").decode P.program_bundle_bytes =
        some (.bundle broot bcat [g]) ∧
      CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat ∧
      CanonicalObjectAt (objSchema 19 profile) ⟨3, 19, grp⟩ g ∧
      (objSchema 19 profile).decode g = some (.group prg ext fns) ∧
      ext.length = 0 ∧ m < fns.length ∧
      (progCheck F ⟨fns, [], catalogOf bcat, m⟩).toOption.isSome = true :=
  h

/-- `ProgramAtAt` decides `programAtDec` on the program's own fields. -/
theorem programAtDec_of_programAtAt {profile : String} {F : Int}
    {P : BoundCoreProgram profile} (h : ProgramAtAt F P) :
    programAtDec F profile P.program_root_ref P.program_root_bytes
      P.program_bundle_ref P.program_bundle_bytes = true := by
  obtain ⟨pr, cat, grp, m, broot, bcat, g, prg, ext, fns, hrd, hbd, hc1, hc2,
    hgd, hext, hentry, hck⟩ := h
  obtain ⟨bcat', gs', hexact⟩ := P.bundle_root_exact
  rw [hbd] at hexact
  cases hexact
  unfold programAtDec
  rw [hrd, hbd]
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨by simpa using P.program_root_at,
      by simpa using P.program_bundle_at⟩, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨beq_self_eq_true _, by simpa using hc1⟩, by simpa using hc2⟩, ?_⟩
  unfold programAtDecGroup
  rw [hgd]
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨by simp [hext], by rw [decide_eq_true_eq]; exact hentry⟩, hck⟩

/-! ## The assembled program -/

/-- Under `ProgramAtAt`, `P.prog` is the typed entry program: the group's
    functions, the bundle's catalog, the root's member — the same
    `RawProg` `bpProgram` reports in `.bound`. -/
theorem programAtAt_prog {profile : String} {F : Int}
    {P : BoundCoreProgram profile} (h : ProgramAtAt F P) :
    ∃ fns cat m, P.prog = ⟨fns, [], cat, m⟩ ∧ m < fns.length ∧ 0 ≤ m ∧
      (progCheck F P.prog).toOption.isSome = true := by
  obtain ⟨pr, cat0, grp, m, broot, bcat, g, prg, ext, fns, hrd, hbd, _, _,
    hgd, hext, hentry, hck⟩ := h
  have hprog : P.prog = ⟨fns, [], catalogOf bcat, m⟩ := by
    unfold BoundCoreProgram.prog
    rw [hrd, hbd]
    dsimp only
    rw [show ([g]).headD "" = g from rfl, hgd]
  refine ⟨fns, catalogOf bcat, m, hprog, hentry, progCheck_isOk_entry hck, ?_⟩
  rw [hprog]
  exact hck

/-- The `ProgramAt`-level version: the assembled program, its entry in
    range and nonnegative, and `progCheck` acceptance at the witness
    fuel. -/
theorem programAt_prog {profile : String} {P : BoundCoreProgram profile}
    (h : ProgramAt P) :
    ∃ F fns cat m, P.prog = ⟨fns, [], cat, m⟩ ∧ m < fns.length ∧ 0 ≤ m ∧
      (progCheck F P.prog).toOption.isSome = true := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨fns, cat, m, hp, he, hm, hck⟩ := programAtAt_prog hF
  exact ⟨F, fns, cat, m, hp, he, hm, hck⟩

/-! ## Teeth -/

/-- The bundle's stored root-bytes field IS the program root's bytes —
    what `bundle_root_exact` means applied to a decoded bundle. -/
theorem BoundCoreProgram.bundle_root_exact_eq {profile : String}
    (P : BoundCoreProgram profile) {broot bcat : String} {gs : List String}
    (hd : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs)) : broot = P.program_root_bytes := by
  obtain ⟨bcat', gs', hd'⟩ := P.bundle_root_exact
  rw [hd'] at hd
  cases hd
  rfl

/-- No `BoundCoreProgram` has a bundle whose stored root differs —
    `bundle_root_exact` has teeth (corpus row 26's
    `[rcic_scm_bp_root_mismatch]`). -/
theorem bundle_mismatch_no_bound {profile : String}
    {rb bb : String} {broot bcat : String} {gs : List String}
    (hd : (objSchema 21 "").decode bb = some (.bundle broot bcat gs))
    (hne : broot ≠ rb) :
    ¬ ∃ (P : BoundCoreProgram profile),
      P.program_root_bytes = rb ∧ P.program_bundle_bytes = bb := by
  rintro ⟨P, hrb, hbb⟩
  rw [← hbb] at hd
  have heq := P.bundle_root_exact_eq hd
  rw [hrb] at heq
  exact hne heq

/-- A root under another profile is no canonical program root at this
    profile's schema — the §6 profile-consistency tooth (corpus rows 19,
    35). -/
theorem canonicalObjectAt_root_profile {profile : String} {r : Ref}
    {b : String} {pr cat grp : String} {m : Int}
    (hd : (objSchema 20 profile).decode b = some (.root pr cat grp m))
    (hne : pr ≠ profile) : ¬ CanonicalObjectAt (objSchema 20 profile) r b := by
  rintro ⟨h1, _, _⟩
  rw [hd] at h1
  obtain ⟨_, hcons⟩ := h1
  have hcons2 : (r.cls == 3 && r.kind == 20 &&
    ((20 : Int) == 18 || pr == profile)) = true := hcons
  rw [Bool.and_eq_true, Bool.and_eq_true] at hcons2
  obtain ⟨⟨_, _⟩, hor⟩ := hcons2
  exact (Bool.or_eq_true_iff.mp hor).elim
    (fun h18 => absurd h18 (by decide))
    (fun hpr => hne (eq_of_beq hpr))

/-- A catalog out of §6 order decodes at the object layer but has no
    canonical binding — the order-gate tooth (corpus rows 9, 37). -/
theorem canonicalObjectAt_catalog_order {r : Ref} {b : String}
    {c : List CatalogEntry}
    (hd : objDec b.length 18 b = .ok (.catalog c, b.length))
    (hord : catalogCanonical c = false) :
    ¬ CanonicalObjectAt (objSchema 18 "") r b := by
  intro hC
  have hdec : (objSchema 18 "").decode b = none := by
    unfold objSchema
    dsimp only
    rw [hd]
    dsimp only
    have hcc : catalogCanonical (objCatalog (.catalog c)) = false := hord
    rw [if_pos ⟨rfl, by simp [hcc]⟩]
  unfold CanonicalObjectAt at hC
  rw [hdec] at hC
  exact hC.1.elim

/-- The `ext`-closure tooth: a group carrying external signatures cannot
    satisfy `ProgramAtAt` (corpus row 31's `[rcic_scm_bp_external]`). -/
theorem programAtAt_ext_refused {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {broot bcat g prg : String}
    {ext : List ExtSig} {fns : List RawFnDef}
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hg : (objSchema 19 profile).decode g = some (.group prg ext fns))
    (hne : ext.length ≠ 0) : ¬ ProgramAtAt F P := by
  intro h
  obtain ⟨pr, cat, grp, m, broot', bcat', g', prg', ext', fns', hrd, hb',
    hc1, hc2, hg', hext', hentry', hck⟩ := h
  rw [hb] at hb'
  cases hb'
  rw [hg] at hg'
  cases hg'
  exact hne hext'

/-- The `∃F` lift: `ProgramAt` itself refuses an external-signature
    group. -/
theorem programAt_ext_refused {profile : String}
    {P : BoundCoreProgram profile} {broot bcat g prg : String}
    {ext : List ExtSig} {fns : List RawFnDef}
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hg : (objSchema 19 profile).decode g = some (.group prg ext fns))
    (hne : ext.length ≠ 0) : ¬ ProgramAt P :=
  fun ⟨_F, h⟩ => programAtAt_ext_refused hb hg hne h

/-- The one-group tooth: a bundle whose group list is not a singleton
    cannot satisfy `ProgramAtAt` (corpus rows 29–30's
    `[rcic_scm_bp_closure]`). -/
theorem programAtAt_closure_refused {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {broot bcat : String} {gs : List String}
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs))
    (hgs : gs.length ≠ 1) : ¬ ProgramAtAt F P := by
  intro h
  obtain ⟨pr, cat, grp, m, broot', bcat', g', prg', ext', fns', hrd, hb',
    hc1, hc2, hg', hext', hentry', hck⟩ := h
  rw [hb] at hb'
  cases hb'
  exact hgs rfl

/-- The `∃F` lift: `ProgramAt` refuses a non-singleton group list. -/
theorem programAt_closure_refused {profile : String}
    {P : BoundCoreProgram profile} {broot bcat : String} {gs : List String}
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs))
    (hgs : gs.length ≠ 1) : ¬ ProgramAt P :=
  fun ⟨_F, h⟩ => programAtAt_closure_refused hb hgs h

/-- The entry tooth: a root member outside the group's function list
    cannot satisfy `ProgramAtAt` (corpus row 32's
    `[rcic_scm_bp_entry]`). -/
theorem programAtAt_entry_refused {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pr cat grp : String} {m : Int}
    {broot bcat g prg : String} {ext : List ExtSig} {fns : List RawFnDef}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hg : (objSchema 19 profile).decode g = some (.group prg ext fns))
    (hm : ¬ m < fns.length) : ¬ ProgramAtAt F P := by
  intro h
  obtain ⟨pr', cat', grp', m', broot', bcat', g', prg', ext', fns', hrd', hb',
    hc1, hc2, hg', hext', hentry', hck⟩ := h
  rw [hrd] at hrd'
  cases hrd'
  rw [hb] at hb'
  cases hb'
  rw [hg] at hg'
  cases hg'
  exact hm hentry'

/-- The `∃F` lift: `ProgramAt` refuses an out-of-range entry member. -/
theorem programAt_entry_refused {profile : String}
    {P : BoundCoreProgram profile} {pr cat grp : String} {m : Int}
    {broot bcat g prg : String} {ext : List ExtSig} {fns : List RawFnDef}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hg : (objSchema 19 profile).decode g = some (.group prg ext fns))
    (hm : ¬ m < fns.length) : ¬ ProgramAt P :=
  fun ⟨_F, h⟩ => programAtAt_entry_refused hrd hb hg hm h

/-- The catalog tooth: when the catalog the root names is not bound
    canonically, `ProgramAtAt` fails (corpus rows 27, 37's
    `[rcic_scm_obj_digest]`/`[rcic_scm_bp_catalog_order]`). -/
theorem programAtAt_catalog_refused {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pr cat grp : String} {m : Int}
    {broot bcat g : String}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hc : ¬ CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat) :
    ¬ ProgramAtAt F P := by
  intro h
  obtain ⟨pr', cat', grp', m', broot', bcat', g', prg', ext', fns', hrd', hb',
    hc', hc2, hg', hext', hentry', hck⟩ := h
  rw [hrd] at hrd'
  cases hrd'
  rw [hb] at hb'
  cases hb'
  exact hc hc'

/-- The `∃F` lift: `ProgramAt` refuses an unbound named catalog. -/
theorem programAt_catalog_refused {profile : String}
    {P : BoundCoreProgram profile} {pr cat grp : String} {m : Int}
    {broot bcat g : String}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hb : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat [g]))
    (hc : ¬ CanonicalObjectAt (objSchema 18 "") ⟨3, 18, cat⟩ bcat) :
    ¬ ProgramAt P :=
  fun ⟨_F, h⟩ => programAtAt_catalog_refused hrd hb hc h

end Rcic.Scm.BoundProgAt

/-! ## Pins: apps/rcic-scm-bound-program/rcic_scm_bound_program_corpus.json

Every pin is native (`#guard`): the propositions are decided at each
object's own fuel on the corpus rows, and each refusal tooth is pinned
beside the same row's carrier refusal (`agrees3` cross-checks the decider
against `scmBP` form 3). The program-check closure is exercised by
`progCheck` itself at the corpus fuel (kernel-computable). -/

namespace Rcic.Scm.BoundProgAt.Pins
open Rcic.Scm Rcic.Scm.Wire Rcic.BoundObject Rcic.Scm.BoundProg
open Rcic.Scm.BoundProg.Pins Rcic.Scm.BoundProgAt

def PB0 : Parts := parts { PROG with entry := 0 }
def U2 : String := objEnc (.bundle rb cb [gb, gb])
def U0 : String := objEnc (.bundle rb cb [])
def PE : Parts := parts PROG_EXT
def P5 : Parts := parts PROG (member := 5)
def PBAD : Parts := parts PROG_BAD
def PRZ : Parts := parts PROG_RAISE
def PP1 : Parts := parts PROG P1
def PG1 : Parts := parts PROG (gprofile := P1)
def PU : Parts := parts PROG (cat := CAT.reverse)

/-- The schema decode at its declared `Obj` type, so `#guard`'s `==`
    resolves `BEq (Option Obj)` (the `ObjSchema.Obj` projection does not
    reduce for instance search). -/
def decObj (k : Int) (p : String) (b : String) : Option Obj :=
  (objSchema k p).decode b

/-- The decider's agreement with `scmBP` form 3 on a row. -/
def agrees3 (rr : Ref) (rb : String) (br : Ref) (bb : String) : Bool :=
  programAtDec 64 P0 rr rb br bb ==
    ((scmBP 3 64 P0 rr rb br bb emptyProg).ok == 1)

-- BP0 the corpus program is a bound program: form 3 accepts (row 23)
#guard f3p Pp == bpOk (.bound PROG I)
-- BP1 its members bind at their own fuel (the Prop-side evidence)
#guard (bpMember rb.length P0 (rf rb 20) 20 rb).ok == 1
#guard (objBind bb.length (rf bb 21) 21 bb).ok == 1
#guard (bpCatalog cb.length (rf cb 18) cb).ok == 1
#guard (bpMember gb.length P0 (rf gb 19) 19 gb).ok == 1
-- BP2 the own-fuel decodes give the form-3 shapes
#guard decObj 20 P0 rb == some (.root P0 (dg cb 18) (dg gb 19) 1)
#guard decObj 21 "" bb == some (.bundle rb cb [gb])
#guard decObj 18 "" cb == some (.catalog CAT)
#guard decObj 19 P0 gb == some (.group P0 [] PROG.fns)
-- BP3 the decider accepts the corpus program at its corpus fuel
#guard programAtDec 64 P0 (rf rb 20) rb (rf bb 21) bb
-- BP4 and the every-family program (row 39's data; entry member 0)
#guard programAtDec 64 P0 (rf PA.rb 20) PA.rb (rf PA.bb 21) PA.bb
-- BP5 the assembled programs type-check at the corpus fuel
#guard (progCheck 64 ⟨PROG.fns, [], CAT, 1⟩).toOption.isSome
#guard (progCheck 64 ⟨PROG_ALL.fns, [], CAT, 0⟩).toOption.isSome

-- BP-T0 the mismatched bundle decodes to a bundle over a DIFFERENT root
--   (`bundle_mismatch_no_bound`'s premise; row 26)
#guard decObj 21 "" PB0.bb == some (.bundle PB0.rb PB0.cb [PB0.gb])
#guard PB0.rb != rb
#guard !programAtDec 64 P0 (rf rb 20) rb (rf PB0.bb 21) PB0.bb
    && agrees3 (rf rb 20) rb (rf PB0.bb 21) PB0.bb
-- BP-T1 a two-group bundle: the one-group closure refuses (row 29)
#guard decObj 21 "" U2 == some (.bundle rb cb [gb, gb])
#guard !programAtDec 64 P0 (rf rb 20) rb (rf U2 21) U2
    && agrees3 (rf rb 20) rb (rf U2 21) U2
-- BP-T2 an empty group list (row 30)
#guard decObj 21 "" U0 == some (.bundle rb cb [])
#guard !programAtDec 64 P0 (rf rb 20) rb (rf U0 21) U0
    && agrees3 (rf rb 20) rb (rf U0 21) U0
-- BP-T3 an external-signature group: the `ext.length = 0` tooth (row 31)
#guard decObj 19 P0 GX == some (.group P0 EXT PROG_EXT.fns)
#guard !programAtDec 64 P0 (rf PE.rb 20) PE.rb (rf PE.bb 21) PE.bb
    && agrees3 (rf PE.rb 20) PE.rb (rf PE.bb 21) PE.bb
-- BP-T4 entry member out of range (row 32)
#guard !programAtDec 64 P0 (rf P5.rb 20) P5.rb (rf P5.bb 21) P5.bb
    && agrees3 (rf P5.rb 20) P5.rb (rf P5.bb 21) P5.bb
-- BP-T5 an ill-typed program: `progCheck` refuses (row 33)
#guard !programAtDec 64 P0 (rf PBAD.rb 20) PBAD.rb (rf PBAD.bb 21) PBAD.bb
    && agrees3 (rf PBAD.rb 20) PBAD.rb (rf PBAD.bb 21) PBAD.bb
-- BP-T6 a residue ref outside the catalog: `progCheck` refuses (row 34)
#guard !programAtDec 64 P0 (rf PRZ.rb 20) PRZ.rb (rf PRZ.bb 21) PRZ.bb
    && agrees3 (rf PRZ.rb 20) PRZ.rb (rf PRZ.bb 21) PRZ.bb
-- BP-T7 a program under another profile: root consistency refuses (row 35)
#guard !programAtDec 64 P0 (rf PP1.rb 20) PP1.rb (rf PP1.bb 21) PP1.bb
    && agrees3 (rf PP1.rb 20) PP1.rb (rf PP1.bb 21) PP1.bb
-- BP-T8 group profile ≠ program profile: group consistency refuses (row 36)
#guard !programAtDec 64 P0 (rf PG1.rb 20) PG1.rb (rf PG1.bb 21) PG1.bb
    && agrees3 (rf PG1.rb 20) PG1.rb (rf PG1.bb 21) PG1.bb
-- BP-T9 an unsorted catalog: the §6 order gate refuses (row 37)
#guard !programAtDec 64 P0 (rf PU.rb 20) PU.rb (rf PU.bb 21) PU.bb
    && agrees3 (rf PU.rb 20) PU.rb (rf PU.bb 21) PU.bb
-- BP-T10 digest mismatches on the root/bundle refs (rows 24, 25)
#guard !programAtDec 64 P0 (rf R1 20) rb (rf bb 21) bb
    && agrees3 (rf R1 20) rb (rf bb 21) bb
#guard !programAtDec 64 P0 (rf rb 20) rb (rf rb 21) bb
    && agrees3 (rf rb 20) rb (rf rb 21) bb
-- BP-T11 the composed agreement holds on the accepting rows too
#guard agrees3 (rf rb 20) rb (rf bb 21) bb
#guard agrees3 (rf PA.rb 20) PA.rb (rf PA.bb 21) PA.bb

end Rcic.Scm.BoundProgAt.Pins
