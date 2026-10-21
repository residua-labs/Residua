/-
RCIC 06 §7/§18 SCM-015 — `ProgramBundleAtProf`: the "and profiles"
conjunct over the landed `ProgramAtAtCl` closure
(`ScmBoundProgramCl.lean`, #6594). The scm-side decider is the sealed
carrier `apps/rcic-scm-bundle-profiles` (S0:
`research/rcic/scm/S0_SCM015_PROFILES.md`, segment S3).

Owner text: 06 §7 "A closed core-program bundle contains the root,
residue catalog, and the exact transitive closure of function groups
and profiles"; §18 same enumeration as the mandatory bundle witness;
06:120,142 `scm_semantics_profile_ref` is a *ref* field of
`CoreFunctionGroupCandidate` and `CoreProgramRoot`.

TRANSCRIPTION TABLE (06/carrier → Lean):
  `kind:profile` canonical `k:v` object        → `profBound`:
        `CanonicalObjectAt kvSchema ⟨3, 0, prof⟩ pb` (the carrier's kind-0
        convention — NO `objSchema` kind was added; the sealed codec is
        untouched) ∧ `partAt pb "kind" = "profile"`
  profile→profile deps (`refs` edge)           → `profDeps`: the `refs`
        part as a comma-list, `""` ↦ `[]` — `rcic.cog_bundle_refs_list`'s
        reading
  transitive closure over profile deps         → `profClosure`: the same
        bounded-pass fixpoint shape as `closureSet`; `ProfReach` is the
        declarative reading (the `extStep`/`ReachCl` pattern — the
        membership→reach direction is proven in `profSteps_reach`; the
        bounded-pass completeness direction stays open, the same gap the
        base file leaves between `closureSet` and `ReachCl`)
  every member's `scm_semantics_profile_ref`   → `memberProfs`: the
        decoded root's `pr` plus each `clGroups` member's `prg` — the
        carrier's seed set. Under the schema's profile consistency these
        all equal the ambient `profile` (`memberProfs_eq_profile`)
  seed bound + closure bound                   → `profsInstalled`
        (closure-membership reading) and `profsInstalledDec` (the Bool)

[spec_ambiguity] carried from the S0: 06 gives no profile-object bytes.
The prop is stated over the landed carrier's `kind:profile|refs:` `k:v`
convention — the same registry shape `rcic-program-bundle` seals.
-/

import rcic.ScmBoundProgramCl
import rcic.ScmEmbed

namespace Rcic.Scm.BoundProgAt
open Rcic.Scm Rcic.Scm.BoundProg Rcic.Scm.Wire Rcic.BoundObject

/-! ## The profile object and its dep edge -/

/-- `rcic.cog_bundle_refs_list` at the profile object: the `refs` part as
    a dep list, `""` ↦ `[]`. -/
def profDeps (pb : String) : List String :=
  let rv := Rcic.Scm.Embed.partAt pb "refs"
  if rv = "" then [] else rv.splitOn ","

/-- `prof` names a bound profile object in `pstore`: some member is
    canonical at kind 0 under `kvSchema` at the `prof` address AND tagged
    `kind:profile` — the carrier's `scm_bundle_prof_bound_all` check. -/
def profBound (pstore : List String) (prof : String) : Prop :=
  ∃ pb ∈ pstore, CanonicalObjectAt kvSchema ⟨3, 0, prof⟩ pb ∧
    Rcic.Scm.Embed.partAt pb "kind" = "profile"

/-- The Bool half: a bound `kind:profile` candidate exists in `pstore`. -/
def profBoundDec (pstore : List String) (prof : String) : Bool :=
  pstore.any fun pb =>
    decide (CanonicalObjectAt kvSchema ⟨3, 0, prof⟩ pb) &&
    (Rcic.Scm.Embed.partAt pb "kind" == "profile")

/-! ## The closure computation (the `reachStep`/`closureSet` shape) -/

/-- One expansion pass: every profile object whose derived kind-0 digest
    is seen contributes its dep digests. -/
def profStepPass (pstore : List String) (seen : List String) : List String :=
  pstore.foldl (fun a pb =>
    if dg pb 0 ∈ seen then a ++ profDeps pb else a) seen

/-- `n` expansion passes over the seen set. -/
def profSteps (pstore : List String) : Nat → List String → List String
  | 0, s => s
  | n + 1, s => profStepPass pstore (profSteps pstore n s)

/-- The reachable profile digest set from `seeds` over `pstore`'s dep
    edges — `|pstore|` passes: every simple dep chain has at most
    `|pstore|` distinct member sources. -/
def profClosure (pstore : List String) (seeds : List String) : List String :=
  profSteps pstore pstore.length seeds

/-- The declarative profile→profile dep edge (the `extStep` reading). -/
def profStep (pstore : List String) (p q : String) : Prop :=
  ∃ pb ∈ pstore, dg pb 0 = p ∧ q ∈ profDeps pb

/-- Profile reachability from any seed (the `ReachCl` reading). `seeds`
    is an index so `profReach_mono` can induct. -/
inductive ProfReach (pstore : List String) : List String → String → Prop
  | seed {seeds : List String} {q : String} : q ∈ seeds →
      ProfReach pstore seeds q
  | dep {seeds : List String} {q r : String} : ProfReach pstore seeds q →
      profStep pstore q r → ProfReach pstore seeds r

/-- The profile-installation conjunct (06 §7/§18 "and profiles"): every
    digest in the computed dep-closure of the named seeds is a bound
    `kind:profile` object. -/
def profsInstalled (pstore : List String) (seeds : List String) : Prop :=
  ∀ q ∈ profClosure pstore seeds, profBound pstore q

/-- The installation decision over the computed closure — the carrier's
    seed-bind + members-bound fold. -/
def profsInstalledDec (pstore : List String) (seeds : List String) : Bool :=
  (profClosure pstore seeds).all (profBoundDec pstore)

/-! ## The conjunct -/

/-- The profile refs named inside the decoded root and group bytes:
    the root's `pr` plus each group's `prg`. -/
def memberProfsOf (profile : String) (rb bb : String) : List String :=
  match (objSchema 20 profile).decode rb,
        (objSchema 21 "").decode bb with
  | some (.root pr _ _ _), some (.bundle _ _ gs) =>
      pr :: (clGroups profile gs).map (·.prg)
  | _, _ => []

/-- The profile refs the closed bundle's members name — the carrier's
    seed set. -/
def memberProfs {profile : String} (P : BoundCoreProgram profile) : List String :=
  memberProfsOf profile P.program_root_bytes P.program_bundle_bytes

/-- `ProgramAtAtCl` plus "and profiles": the landed multi-group closure
    AND every profile the bundle's members name bound transitively in the
    presented profile store. -/
def ProgramAtAtClProf {profile : String} (F : Int)
    (P : BoundCoreProgram profile) (pstore : List String) : Prop :=
  ProgramAtAtCl F P ∧ profsInstalled pstore (memberProfs P)

/-- The census row's remaining conjunct (SCM-015): the closed bundle's
    profile side holds at some program-check fuel. -/
def ProgramBundleAtProf {profile : String} (P : BoundCoreProgram profile)
    (pstore : List String) : Prop :=
  ∃ F : Int, ProgramAtAtCl F P ∧ profsInstalled pstore (memberProfs P)

/-- The whole form-0 instrument over the carrier's raw inputs:
    `programAtClDec` on the bundle AND `profsInstalledDec` on the
    presented profile store. -/
def programBundleProfDec (F : Int) (profile : String)
    (rr : Ref) (rb : String) (br : Ref) (bb : String)
    (pstore : List String) : Bool :=
  programAtClDec F profile rr rb br bb &&
  profsInstalledDec pstore (memberProfsOf profile rb bb)

/-! ## Fold lemmas -/

/-- `acc`'s members survive the stepper fold (the stepper only appends). -/
theorem mem_foldl_stepper {pstore : List String} {seen : List String}
    {acc : List String} {x : String} (h : x ∈ acc) :
    x ∈ pstore.foldl (fun a pb =>
      if dg pb 0 ∈ seen then a ++ profDeps pb else a) acc := by
  induction pstore generalizing acc with
  | nil => exact h
  | cons pb rest ih =>
    apply ih
    dsimp only
    by_cases hc : dg pb 0 ∈ seen
    · rw [if_pos hc]; exact List.mem_append.mpr (Or.inl h)
    · rw [if_neg hc]; exact h

/-- A new element of a stepper fold is either old or a dep of a seen
    member. -/
theorem mem_foldl_stepper_or {pstore : List String} {seen acc : List String}
    {x : String} (h : x ∈ pstore.foldl (fun a pb =>
      if dg pb 0 ∈ seen then a ++ profDeps pb else a) acc) :
    x ∈ acc ∨ ∃ pb ∈ pstore, dg pb 0 ∈ seen ∧ x ∈ profDeps pb := by
  induction pstore generalizing acc with
  | nil => exact Or.inl h
  | cons pb rest ih =>
    have h' := ih h
    cases h' with
    | inl hacc =>
      dsimp only at hacc
      by_cases hc : dg pb 0 ∈ seen
      · rw [if_pos hc] at hacc
        cases List.mem_append.mp hacc with
        | inl ha => exact Or.inl ha
        | inr hd => exact Or.inr ⟨pb, List.mem_cons_self _ _, hc, hd⟩
      · rw [if_neg hc] at hacc; exact Or.inl hacc
    | inr he =>
      obtain ⟨pb', hpb', hdg, hd⟩ := he
      exact Or.inr ⟨pb', List.mem_cons_of_mem _ hpb', hdg, hd⟩

/-- A dep of a seen member enters the fold no matter the starting `acc`. -/
theorem mem_foldl_stepper_dep {pstore : List String} {seen : List String}
    {pb q : String} (h : dg pb 0 ∈ seen)
    (hpb : pb ∈ pstore) (hq : q ∈ profDeps pb) :
    ∀ acc : List String, q ∈ pstore.foldl (fun a pb' =>
      if dg pb' 0 ∈ seen then a ++ profDeps pb' else a) acc := by
  induction pstore with
  | nil => exact absurd hpb (List.not_mem_nil _)
  | cons x xs ih =>
    intro acc
    rw [List.foldl_cons]
    cases List.mem_cons.mp hpb with
    | inl he =>
      subst he
      apply mem_foldl_stepper
      dsimp only
      rw [if_pos h]; exact List.mem_append.mpr (Or.inr hq)
    | inr htail => exact ih htail _

/-- `seen`'s members survive one pass. -/
theorem mem_profStepPass {pstore seen : List String} {x : String}
    (h : x ∈ seen) : x ∈ profStepPass pstore seen :=
  mem_foldl_stepper h

/-- `seen`'s members survive `n` passes. -/
theorem mem_profSteps {pstore seen : List String} {x : String}
    (h : x ∈ seen) : ∀ n : Nat, x ∈ profSteps pstore n seen := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact mem_profStepPass ih

/-- A seed is in the closure. -/
theorem mem_profClosure_seed {pstore seeds : List String} {s : String}
    (h : s ∈ seeds) : s ∈ profClosure pstore seeds :=
  mem_profSteps h _

/-- A dep of a seen member enters at the next pass. -/
theorem mem_profStepPass_dep {pstore seen : List String} {pb q : String}
    (h : dg pb 0 ∈ seen) (hpb : pb ∈ pstore) (hq : q ∈ profDeps pb) :
    q ∈ profStepPass pstore seen :=
  mem_foldl_stepper_dep h hpb hq seen

/-- A dep of a pass-`n` member is in the pass-`n+1` table. -/
theorem mem_profSteps_dep {pstore seen : List String} {n : Nat} {pb q : String}
    (h : dg pb 0 ∈ profSteps pstore n seen) (hpb : pb ∈ pstore)
    (hq : q ∈ profDeps pb) : q ∈ profSteps pstore (n + 1) seen :=
  mem_profStepPass_dep h hpb hq

/-- Soundness of the table: a digest in `profSteps` after `n` passes is
    reachable from a seed. -/
theorem profSteps_reach {pstore seen : List String} :
    ∀ {n : Nat} {q : String}, q ∈ profSteps pstore n seen →
      ProfReach pstore seen q := by
  intro n
  induction n with
  | zero => intro q h; exact ProfReach.seed h
  | succ n ih =>
    intro q h
    have := mem_foldl_stepper_or h
    cases this with
    | inl hprev => exact ih hprev
    | inr he =>
      obtain ⟨pb, hpb, hdg, hd⟩ := he
      exact ProfReach.dep (ih hdg) ⟨pb, hpb, rfl, hd⟩

/-- Reachability enters some pass table (the unbounded completeness
    direction; the `|pstore|`-pass bound is the part the base file also
    leaves open for `closureSet`/`ReachCl`). -/
theorem profReach_steps {pstore : List String} {seeds : List String}
    {q : String} (h : ProfReach pstore seeds q) :
    ∃ n : Nat, q ∈ profSteps pstore n seeds := by
  induction h with
  | seed hq => exact ⟨0, hq⟩
  | dep hr hstep ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨pb, hpb, hdg, hd⟩ := hstep
    exact ⟨n + 1, mem_profSteps_dep (hdg ▸ hn) hpb hd⟩

/-- Reachability is monotone in the seed set. -/
theorem profReach_mono {pstore : List String} {seeds seeds' : List String}
    {q : String} (hs : seeds ⊆ seeds') (h : ProfReach pstore seeds q) :
    ProfReach pstore seeds' q := by
  induction h with
  | seed hq => exact ProfReach.seed (hs hq)
  | dep hr hstep ih => exact ProfReach.dep ih hstep

/-! ## The `profsInstalled` conjunct and its instrument -/

/-- A decided candidate pays `profBound`. -/
theorem profBound_of_dec {pstore : List String} {prof : String}
    (h : profBoundDec pstore prof = true) : profBound pstore prof := by
  unfold profBoundDec at h
  rw [List.any_eq_true] at h
  obtain ⟨pb, hpb, hdec⟩ := h
  rw [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hdec
  exact ⟨pb, hpb, hdec.1, hdec.2⟩

/-- `profsInstalledDec` decided yields `profsInstalled`. -/
theorem profsInstalled_of_dec {pstore seeds : List String}
    (h : profsInstalledDec pstore seeds = true) :
    profsInstalled pstore seeds := fun q hq =>
  profBound_of_dec (List.all_eq_true.mp h q hq)

/-- A named seed is bound when installed. -/
theorem profsInstalled_seed {pstore seeds : List String} {s : String}
    (hi : profsInstalled pstore seeds) (h : s ∈ seeds) :
    profBound pstore s :=
  hi s (mem_profClosure_seed h)

/-! ## `memberProfs` facts -/

/-- The decoded root's `pr` is a member profile. -/
theorem mem_memberProfs_root {profile : String} {P : BoundCoreProgram profile}
    {pr cat grp broot bcat : String} {m : Int} {gs : List String}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hbd : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs)) :
    pr ∈ memberProfs P := by
  show pr ∈ memberProfsOf profile P.program_root_bytes P.program_bundle_bytes
  unfold memberProfsOf
  rw [hrd, hbd]
  exact List.mem_cons_self _ _

/-- A decoded group member's `prg` is a member profile. -/
theorem mem_memberProfs_group {profile : String}
    {P : BoundCoreProgram profile} {cg : ClGroup}
    {pr cat grp broot bcat : String} {m : Int} {gs : List String}
    (hrd : (objSchema 20 profile).decode P.program_root_bytes =
      some (.root pr cat grp m))
    (hbd : (objSchema 21 "").decode P.program_bundle_bytes =
      some (.bundle broot bcat gs))
    (hcg : cg ∈ clGroups profile gs) :
    cg.prg ∈ memberProfs P := by
  show cg.prg ∈ memberProfsOf profile P.program_root_bytes
    P.program_bundle_bytes
  unfold memberProfsOf
  rw [hrd, hbd]
  exact List.mem_cons_of_mem _ (List.mem_map_of_mem (·.prg) hcg)

/-- Under `ProgramAtAtCl`, every named member profile is the ambient
    `profile` — the schema's profile consistency. The per-member reading
    collapses, which is exactly 06:120,142's "the" semantics profile. -/
theorem memberProfs_eq_profile {profile : String} {F : Int}
    {P : BoundCoreProgram profile} (h : ProgramAtAtCl F P) :
    ∀ prof ∈ memberProfs P, prof = profile := by
  obtain ⟨pr, cat, grp, m, broot, bcat, gs, hrd, hbd, hc1, hne, hnd, hbind,
    hentry, hres, hreach, hbods⟩ := h
  have hmp : memberProfs P = pr :: (clGroups profile gs).map (·.prg) := by
    show memberProfsOf profile P.program_root_bytes P.program_bundle_bytes =
      pr :: (clGroups profile gs).map (·.prg)
    unfold memberProfsOf
    rw [hrd, hbd]
  intro prof hp
  rw [hmp] at hp
  cases List.mem_cons.mp hp with
  | inl he =>
    subst he
    have hcons := (P.program_root_at).1
    rw [hrd] at hcons
    obtain ⟨_, hcons⟩ := hcons
    simp only [objSchema, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hcons
    -- hcons.2 : (20 : Int) = 18 ∨ objProfile (.root prof cat grp m) = profile
    cases hcons.2 with
    | inl hb => exact absurd hb (by decide)
    | inr hb => simp only [objProfile] at hb; exact hb
  | inr hm =>
    obtain ⟨cg, hcg, hprg⟩ := List.mem_map.mp hm
    subst hprg
    obtain ⟨hcan, hd⟩ := hbind cg hcg
    obtain ⟨h1, _, _⟩ := hcan
    rw [hd] at h1
    obtain ⟨_, hcons⟩ := h1
    simp only [objSchema, Bool.and_eq_true, Bool.or_eq_true,
      beq_iff_eq] at hcons
    -- hcons.2 : (19 : Int) = 18 ∨ objProfile (.group ..) = profile
    cases hcons.2 with
    | inl hb => exact absurd hb (by decide)
    | inr hb => simp only [objProfile] at hb; exact hb

/-! ## Composition consequences -/

/-- The conjunct projects the landed closure. -/
theorem programAtAtCl_of_programAtAtClProf {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pstore : List String}
    (h : ProgramAtAtClProf F P pstore) : ProgramAtAtCl F P :=
  h.1

theorem programBundleAtCl_of_programBundleAtProf {profile : String}
    {P : BoundCoreProgram profile} {pstore : List String}
    (h : ProgramBundleAtProf P pstore) : ProgramBundleAtCl P := by
  obtain ⟨F, hF, _⟩ := h
  exact ⟨F, hF⟩

/-- Every profile the bundle's members name is bound in the store —
    the direct-clause half of "and profiles". -/
theorem programAtAtClProf_named_bound {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pstore : List String}
    (h : ProgramAtAtClProf F P pstore) :
    ∀ prof ∈ memberProfs P, profBound pstore prof :=
  fun _ hp => profsInstalled_seed h.2 hp

/-- The ambient semantics profile is a named member (via the root's
    `scm_semantics_profile_ref`), hence bound — the carrier's seed-bind
    consequence at the prop level. -/
theorem programAtAtClProf_profile_bound {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pstore : List String}
    (h : ProgramAtAtClProf F P pstore) : profBound pstore profile := by
  obtain ⟨hcl, hinst⟩ := h
  have hcl' := hcl
  obtain ⟨pr, cat, grp, m, broot, bcat, gs, hrd, hbd, _⟩ := hcl
  have hroot : pr ∈ memberProfs P := mem_memberProfs_root hrd hbd
  have hpr : pr = profile := memberProfs_eq_profile hcl' _ hroot
  exact hpr ▸ profsInstalled_seed hinst hroot

/-- A dep edge out of a reachable profile is itself reachable: under
    `ProgramAtAtClProf`, transitively reachable profile digests enter
    some pass table — stated over `profSteps` so the unbounded
    completeness lemma applies honestly. -/
theorem programAtAtClProf_reach {profile : String} {F : Int}
    {P : BoundCoreProgram profile} {pstore : List String} {q : String}
    (_h : ProgramAtAtClProf F P pstore)
    (hr : ProfReach pstore (memberProfs P) q) :
    ∃ n : Nat, q ∈ profSteps pstore n (memberProfs P) :=
  profReach_steps hr

/-- `programBundleProfDec` decided yields a bound program satisfying the
    conjunct — the form-0 ↔ form-2 soundness direction. -/
theorem programAtAtClProf_of_dec {profile : String} {F : Int}
    {rr : Ref} {rb : String} {br : Ref} {bb : String}
    {pstore : List String}
    (h : programBundleProfDec F profile rr rb br bb pstore = true) :
    ∃ P : BoundCoreProgram profile,
      P.program_root_ref = rr ∧ P.program_root_bytes = rb ∧
      P.program_bundle_ref = br ∧ P.program_bundle_bytes = bb ∧
      ProgramAtAtClProf F P pstore := by
  unfold programBundleProfDec at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hcl, hprof⟩ := h
  obtain ⟨P, h1, h2, h3, h4, hP⟩ := programAtAtCl_of_programAtClDec hcl
  refine ⟨P, h1, h2, h3, h4, hP, ?_⟩
  have hmp : memberProfs P = memberProfsOf profile rb bb := by
    show memberProfsOf profile P.program_root_bytes P.program_bundle_bytes =
      memberProfsOf profile rb bb
    rw [h2, h4]
  rw [hmp]
  exact profsInstalled_of_dec hprof

/-! ## Pins

Concrete profile-store fixtures pinned at `#guard` evaluation time — the
same mechanism `RcicBoundObject`'s pins section uses for digest-bearing
bytes, since `deriveDigest` does not reduce in the kernel
(`native_decide` stays forbidden). -/

namespace Pins

/-- A leaf profile object (no deps). -/
def pbLeaf : String := "kind:profile"
/-- A profile object depending on `pbLeaf`. -/
def pbDep : String := "kind:profile|refs:" ++ dg pbLeaf 0
/-- A non-profile `k:v` object. -/
def pbCat : String := "kind:catalog"
def dgLeaf : String := dg pbLeaf 0
def dgDep : String := dg pbDep 0
def dgCat : String := dg pbCat 0

/-- Both closure members bound (`dgDep` → its dep `dgLeaf`). -/
def pinStore : List String := [pbDep, pbLeaf]
/-- The transitive dep `pbLeaf` is absent — the carrier's
    `prof_closure_member_absent` refusal shape. -/
def pinStoreMiss : List String := [pbDep]
/-- The seed binds a non-`kind:profile` object. -/
def pinStoreWrong : List String := [pbCat]

-- positive pin: the seed AND its transitive dep are bound
-- `kind:profile` objects — installed.
#guard profsInstalledDec pinStore [dgDep] == true
-- the seed and its dep each bind as profile objects.
#guard profBoundDec pinStore dgDep == true
#guard profBoundDec pinStore dgLeaf == true

-- refusal: the transitive dep is absent from the store — the
-- "and profiles" transitive clause refuses.
#guard profsInstalledDec pinStoreMiss [dgDep] == false
-- refusal: the seed binds a non-`kind:profile` object.
#guard profsInstalledDec pinStoreWrong [dgCat] == false
-- refusal: the seed names an entirely unbound digest.
#guard profsInstalledDec pinStore [dg "kind:profile|refs:x" 0] == false

end Pins

end Rcic.Scm.BoundProgAt
