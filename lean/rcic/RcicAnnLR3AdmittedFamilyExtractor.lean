import rcic.RcicAnnLR3InductiveFamily

/-!
# Choice-free extraction of admitted family data

The catalog is computed from the data-valued `EnvWfA` derivation. Every
record retains the original parameter and index telescopes, the complete
constructor views, their source typing certificates, and an optional
derived recursor. No view or tree is selected from a proposition.

The field walk extracts actual source typing derivations for plain domains
and every inner domain of a functional recursive field. Direct recursion,
functional recursion, and delta-reached recursion remain distinct data.
The exact normalized shape reader is inherited from the admitted views.

This is the source-signature producer. Turning its source typing evidence
into element codes still requires the environment-aware semantic producer.
In particular this file does not assert an arbitrary-field Bisim decoder,
an iota arm, or a fundamental theorem. `closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.AdmittedFamilyExtractor

open Rcic.Declarative

/-- Recursor admission keeps the constructor layout and freshness evidence
that accompanies the stored major/minor view in the admission rule. -/
structure SourceRecursor (I : IotaIfaceA) (E : ResolvedEnvA)
    (f : Nat) (fm : CheckedMemberA) (fv : FamViewA fm)
    (cs : List (GroupCtorA I E f fm fv)) where
  view : GroupRecA I E f fm fv cs
  layout : cs.reverse.map GroupCtorA.ref = List.range' (f + 1) cs.length
  fresh : (groupEnvA E f fm (cs.map GroupCtorA.entry)).members
    (f + 1 + cs.length) = none
  admission : EnvWfA I (groupRecEnvA cs view)

/-- The original admission data, with dependent fields kept as data. -/
structure SourceGroup (I : IotaIfaceA) where
  base : ResolvedEnvA
  baseAdmission : EnvWfA I base
  ref : Nat
  member : CheckedMemberA
  familyClass : member.mclass = .inductiveM
  view : FamViewA member
  constructors : List (GroupCtorA I base ref member view)
  fresh : GroupFreshA base ref member (constructors.map GroupCtorA.entry)
  admission : EnvWfA I (groupEnvA base ref member (constructors.map GroupCtorA.entry))
  recursor : Option (SourceRecursor I base ref member view constructors)

/-- All groups in an admission derivation, newest first. This recursion
does not inspect a bare membership proposition to obtain a group view. -/
def catalog {I : IotaIfaceA} : {E : ResolvedEnvA} → EnvWfA I E → List (SourceGroup I)
  | _, .empty => []
  | _, .axiomM _ _ _ _ hE _ _ _ _ => catalog hE
  | _, .definitionM _ _ _ _ _ hE _ _ _ _ _ _ _ => catalog hE
  | _, .theoremM _ _ _ _ hE _ _ _ _ _ _ _ => catalog hE
  | _, .opaqueM _ _ _ _ _ hE _ _ _ _ _ _ _ => catalog hE
  | _, .group E f fm u hE hcls hbody hcl hT hlvl fv cs hfresh =>
      ⟨E, hE, f, fm, hcls, fv, cs, hfresh,
        .group E f fm u hE hcls hbody hcl hT hlvl fv cs hfresh, none⟩ :: catalog hE
  | _, .groupRec E f fm u hE hcls hbody hcl hT hlvl fv cs hfresh hlay rec hrf =>
      ⟨E, hE, f, fm, hcls, fv, cs, hfresh,
        .group E f fm u hE hcls hbody hcl hT hlvl fv cs hfresh,
        some ⟨rec, hlay, hrf,
          .groupRec E f fm u hE hcls hbody hcl hT hlvl fv cs hfresh hlay rec hrf⟩⟩ :: catalog hE

/-- Every admitted family member has its actual view in the extracted
catalog. The existential proves coverage; it is never eliminated to data. -/
theorem catalog_covers_family {I : IotaIfaceA} :
    {E : ResolvedEnvA} → (hE : EnvWfA I E) →
    ∀ {r : Nat} {m : CheckedMemberA}, E.members r = some m →
      m.mclass = .inductiveM →
      ∃ g ∈ catalog hE, g.ref = r ∧ g.member = m
  | _, .empty, _, _, hm, _ => Option.noConfusion hm
  | _, .axiomM E f A u hE hf hA hcl hlvl, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_family hE hm hcls
  | _, .definitionM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_family hE hm hcls
  | _, .theoremM E f A p hE hf hA hp hclA hclp hlvlA hlvlp, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_family hE hm hcls
  | _, .opaqueM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_family hE hm hcls
  | _, .group E f fm u hE hfc hb hc ht hl fv cs hf, r, m, hm, hcls => by
      rcases members_groupEnvA _ r m hm with ⟨hr, hm⟩ | hm | hm
      · subst r
        subst m
        exact ⟨_, List.mem_cons_self _ _, rfl, rfl⟩
      · obtain ⟨c, _, he⟩ := List.mem_map.mp hm
        have hm : c.member = m := congrArg Prod.snd he
        rw [← hm, c.hcls] at hcls
        cases hcls
      · obtain ⟨g, hg, hgr, hgm⟩ := catalog_covers_family hE hm hcls
        exact ⟨g, List.mem_cons_of_mem _ hg, hgr, hgm⟩
  | _, .groupRec E f fm u hE hfc hb hc ht hl fv cs hf hlay rec hrf, r, m, hm, hcls => by
      unfold groupRecEnvA at hm
      by_cases hr : r = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        exact False.elim (MemberClass.noConfusion (rec.hcls.symm.trans hcls))
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        rcases members_groupEnvA _ r m hm with ⟨hr, hm⟩ | hm | hm
        · subst r
          subst m
          exact ⟨_, List.mem_cons_self _ _, rfl, rfl⟩
        · obtain ⟨c, _, he⟩ := List.mem_map.mp hm
          have hm : c.member = m := congrArg Prod.snd he
          rw [← hm, c.hcls] at hcls
          cases hcls
        · obtain ⟨g, hg, hgr, hgm⟩ := catalog_covers_family hE hm hcls
          exact ⟨g, List.mem_cons_of_mem _ hg, hgr, hgm⟩

/-- Every admitted constructor is retained together with the view of its
own family and its exact typed field telescope. -/
theorem catalog_covers_constructor {I : IotaIfaceA} :
    {E : ResolvedEnvA} → (hE : EnvWfA I E) →
    ∀ {r : Nat} {m : CheckedMemberA}, E.members r = some m →
      m.mclass = .constructorM →
      ∃ g ∈ catalog hE, ∃ c ∈ g.constructors, c.ref = r ∧ c.member = m
  | _, .empty, _, _, hm, _ => Option.noConfusion hm
  | _, .axiomM E f A u hE hf hA hcl hlvl, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_constructor hE hm hcls
  | _, .definitionM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_constructor hE hm hcls
  | _, .theoremM E f A p hE hf hA hp hclA hclp hlvlA hlvlp, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_constructor hE hm hcls
  | _, .opaqueM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_constructor hE hm hcls
  | _, .group E f fm u hE hfc hb hc ht hl fv cs hf, r, m, hm, hcls => by
      rcases members_groupEnvA _ r m hm with ⟨_, hm⟩ | hm | hm
      · subst m
        exact False.elim (MemberClass.noConfusion (hfc.symm.trans hcls))
      · obtain ⟨c, hmem, he⟩ := List.mem_map.mp hm
        exact ⟨_, List.mem_cons_self _ _, c, hmem,
          congrArg Prod.fst he, congrArg Prod.snd he⟩
      · obtain ⟨g, hg, c, hcm, hcr, hct⟩ := catalog_covers_constructor hE hm hcls
        exact ⟨g, List.mem_cons_of_mem _ hg, c, hcm, hcr, hct⟩
  | _, .groupRec E f fm u hE hfc hb hc ht hl fv cs hf hlay rec hrf, r, m, hm, hcls => by
      unfold groupRecEnvA at hm
      by_cases hr : r = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        exact False.elim (MemberClass.noConfusion (rec.hcls.symm.trans hcls))
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        rcases members_groupEnvA _ r m hm with ⟨_, hm⟩ | hm | hm
        · subst m
          exact False.elim (MemberClass.noConfusion (hfc.symm.trans hcls))
        · obtain ⟨c, hmem, he⟩ := List.mem_map.mp hm
          exact ⟨_, List.mem_cons_self _ _, c, hmem,
            congrArg Prod.fst he, congrArg Prod.snd he⟩
        · obtain ⟨g, hg, c, hcm, hcr, hct⟩ := catalog_covers_constructor hE hm hcls
          exact ⟨g, List.mem_cons_of_mem _ hg, c, hcm, hcr, hct⟩

/-- Every admitted recursor retains the exact group constructor list from
which its major and minor telescopes were built. -/
theorem catalog_covers_recursor {I : IotaIfaceA} :
    {E : ResolvedEnvA} → (hE : EnvWfA I E) →
    ∀ {r : Nat} {m : CheckedMemberA}, E.members r = some m →
      m.mclass = .recursorM →
      ∃ g ∈ catalog hE, ∃ rec, g.recursor = some rec ∧
        r = g.ref + 1 + g.constructors.length ∧ m = rec.view.member
  | _, .empty, _, _, hm, _ => Option.noConfusion hm
  | _, .axiomM E f A u hE hf hA hcl hlvl, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_recursor hE hm hcls
  | _, .definitionM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_recursor hE hm hcls
  | _, .theoremM E f A p hE hf hA hp hclA hclp hlvlA hlvlp, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_recursor hE hm hcls
  | _, .opaqueM E f A v u hE hf hA hv hclA hclv hlvlA hlvlv, r, m, hm, hcls => by
      by_cases hr : r = f
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        cases hcls
      · rw [members_extendEnvA_ne E f _ hr] at hm
        exact catalog_covers_recursor hE hm hcls
  | _, .group E f fm u hE hfc hb hc ht hl fv cs hf, r, m, hm, hcls => by
      rcases members_groupEnvA _ r m hm with ⟨_, hm⟩ | hm | hm
      · subst m
        exact False.elim (MemberClass.noConfusion (hfc.symm.trans hcls))
      · obtain ⟨c, _, he⟩ := List.mem_map.mp hm
        have hm : c.member = m := congrArg Prod.snd he
        rw [← hm, c.hcls] at hcls
        cases hcls
      · obtain ⟨g, hg, rec, hr, hrr, hm⟩ := catalog_covers_recursor hE hm hcls
        exact ⟨g, List.mem_cons_of_mem _ hg, rec, hr, hrr, hm⟩
  | _, .groupRec E f fm u hE hfc hb hc ht hl fv cs hf hlay rec hrf, r, m, hm, hcls => by
      unfold groupRecEnvA at hm
      by_cases hr : r = f + 1 + cs.length
      · rw [hr, members_extendEnvA_self] at hm
        cases hm
        exact ⟨_, List.mem_cons_self _ _,
          ⟨rec, hlay, hrf, .groupRec E f fm u hE hfc hb hc ht hl fv cs hf hlay rec hrf⟩,
          rfl, hr, rfl⟩
      · rw [members_extendEnvA_ne _ _ _ hr] at hm
        rcases members_groupEnvA _ r m hm with ⟨_, hm⟩ | hm | hm
        · subst m
          exact False.elim (MemberClass.noConfusion (hfc.symm.trans hcls))
        · obtain ⟨c, _, he⟩ := List.mem_map.mp hm
          have hm : c.member = m := congrArg Prod.snd he
          rw [← hm, c.hcls] at hcls
          cases hcls
        · obtain ⟨g, hg, rec, hr, hrr, hm⟩ := catalog_covers_recursor hE hm hcls
          exact ⟨g, List.mem_cons_of_mem _ hg, rec, hr, hrr, hm⟩

/-- A plain field or a functional field's inner domain, with the source
formation derivation retained at its exact context and universe arity. -/
structure DomainTask (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) where
  context : LCtxA
  type : ExprA
  level : Level
  typed : HasTyA E I n context type (.sort level)

/-- All family-free domain formations, including all dependent inner
binders of functional recursive fields. -/
def domains {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
      FieldsTyA E I n idxTel Γ k fs res → List (DomainTask E I n)
  | _, _, _, _, .nil _ _ _ _ => []
  | _, _, _, _, .plain Γ _ D u _ _ hD tl => ⟨Γ, D, u, hD⟩ :: domains tl
  | _, _, _, _, .drec _ _ _ _ _ _ tl => domains tl
  | _, _, _, _, .frec _ _ _ _ _ _ _ _ hd tl => domains hd ++ domains tl
  | _, _, _, _, .drecD _ _ _ _ _ _ _ tl => domains tl

def domainCount : List FieldA → Nat
  | [] => 0
  | .plain _ _ :: fs => 1 + domainCount fs
  | .drec _ :: fs => domainCount fs
  | .frec _ _ Bs _ :: fs => (1 + Bs.length) + domainCount fs
  | .drecD _ _ :: fs => domainCount fs

theorem domainCount_plain (ds : List (ExprA × Level)) :
    domainCount (ds.map plainA) = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [List.map_cons, plainA, domainCount, ih, List.length_cons,
      Nat.add_comm 1]

/-- Every plain field and every functional inner binder contributes one
retained typing task. No functional telescope is silently discarded. -/
theorem domains_length {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    {idxTel : Nat → ExprA} {Γ : LCtxA} {k : Nat} {fs : List FieldA} {res : List ExprA}
    (h : FieldsTyA E I n idxTel Γ k fs res) :
    (domains h).length = domainCount fs := by
  induction h with
  | nil => rfl
  | plain Γ k D u fs res hD tl ih =>
      simp only [domains, List.length_cons, domainCount, ih, Nat.add_comm 1]
  | drec Γ k is fs res hi tl ih => exact ih
  | frec Γ k B u Bs is fs res hd tl ihd iht =>
      simp only [domains, List.length_append, ihd, iht, domainCount_plain,
        List.length_cons, domainCount, Nat.add_comm 1]
  | drecD Γ k D is fs res hi tl ih => exact ih

/-- Recursive and constructor-result indices, with their actual typed
argument telescope. Functional recursion contributes its inner result. -/
structure IndexTask (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) where
  context : LCtxA
  telescope : ExprA
  arguments : List ExprA
  typed : ArgsTyA E I n context telescope arguments

def indices {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat} {idxTel : Nat → ExprA} :
    {Γ : LCtxA} → {k : Nat} → {fs : List FieldA} → {res : List ExprA} →
      FieldsTyA E I n idxTel Γ k fs res → List (IndexTask E I n)
  | _, _, _, _, .nil Γ k res hres => [⟨Γ, idxTel k, res, hres⟩]
  | _, _, _, _, .plain _ _ _ _ _ _ _ tl => indices tl
  | _, _, _, _, .drec Γ k is _ _ hi tl => ⟨Γ, idxTel k, is, hi⟩ :: indices tl
  | _, _, _, _, .frec _ _ _ _ _ _ _ _ hd tl => indices hd ++ indices tl
  | _, _, _, _, .drecD Γ k _ is _ _ hi tl => ⟨Γ, idxTel k, is, hi⟩ :: indices tl

/-- The four admitted cases retain the data needed for semantic decoding.
In particular a functional field keeps its entire dependent telescope. -/
inductive FieldPlan
  | plain (type : ExprA) (level : Level)
  | direct (indices : List ExprA)
  | functional (first : ExprA × Level) (rest : List (ExprA × Level)) (indices : List ExprA)
  | delta (type : ExprA) (indices : List ExprA)

def plan : FieldA → FieldPlan
  | .plain D u => .plain D u
  | .drec is => .direct is
  | .frec B u Bs is => .functional (B, u) Bs is
  | .drecD D is => .delta D is

def FieldPlan.source : FieldPlan → FieldA
  | .plain D u => .plain D u
  | .direct is => .drec is
  | .functional (B, u) Bs is => .frec B u Bs is
  | .delta D is => .drecD D is

theorem plan_lossless (f : FieldA) : (plan f).source = f := by cases f <;> rfl

def FieldPlan.inner : FieldPlan → List (ExprA × Level)
  | .functional B Bs _ => B :: Bs
  | _ => []

def FieldPlan.shape : FieldPlan → FieldShape
  | .plain _ _ => .nonrecursive
  | .direct _ => .recursive 0
  | .functional _ Bs _ => .recursive (Bs.length + 1)
  | .delta _ _ => .recursive 0

theorem plan_shape (f : FieldA) : (plan f).shape = f.shape := by cases f <;> rfl

def constructorDomains {I : IotaIfaceA} (g : SourceGroup I)
    (c : GroupCtorA I g.base g.ref g.member g.view) : List (DomainTask g.base I g.member.arity) :=
  domains c.view.typed

def constructorIndices {I : IotaIfaceA} (g : SourceGroup I)
    (c : GroupCtorA I g.base g.ref g.member g.view) : List (IndexTask g.base I g.member.arity) :=
  indices c.view.typed

def constructorPlans {I : IotaIfaceA} (g : SourceGroup I)
    (c : GroupCtorA I g.base g.ref g.member g.view) : List FieldPlan :=
  c.view.fields.map plan

theorem constructorPlans_lossless {I : IotaIfaceA} (g : SourceGroup I)
    (c : GroupCtorA I g.base g.ref g.member g.view) :
    (constructorPlans g c).map FieldPlan.source = c.view.fields := by
  have h : ∀ fs : List FieldA, (fs.map plan).map FieldPlan.source = fs := by
    intro fs
    induction fs with
    | nil => rfl
    | cons f fs ih => simp only [List.map_cons, plan_lossless, ih]
  exact h c.view.fields

theorem normalized_shape_exact {I : IotaIfaceA} (g : SourceGroup I)
    (c : GroupCtorA I g.base g.ref g.member g.view) :
    ctorShapesA g.ref g.member.nparamsA (c.member.normA.getD c.member.mtypeA) =
      some ((constructorPlans g c).map FieldPlan.shape) := by
  rw [c.normA_getD, c.view.shapes g.fresh.base]
  congr 1
  simp only [constructorPlans, List.map_map]
  exact List.map_congr_left (fun f _ => (plan_shape f).symm)

/-- Parameter/index telescopes and all field data are supplied by the
actual admitted Nat and parameterized And examples. -/
theorem nat_catalog_control :
    (catalog pinNatBuilt_wf).map SourceGroup.ref = [10] ∧
    ((catalog pinNatBuilt_wf).map fun g => g.view.params) = [[]] ∧
    ((catalog pinNatBuilt_wf).map fun g => g.view.indices) = [[]] := ⟨rfl, rfl, rfl⟩

theorem and_catalog_control :
    (catalog pinAnd_wf).map SourceGroup.ref = [70] ∧
    ((catalog pinAnd_wf).map fun g => g.view.params.length) = [2] := ⟨rfl, rfl⟩

theorem nat_domain_control (I : IotaIfaceA) :
    domains (pinNatSuccViewA I).typed = [] ∧
    (indices (pinNatSuccViewA I).typed).length = 2 := ⟨rfl, rfl⟩

theorem and_domain_control (I : IotaIfaceA) :
    (domains (pinAndMkViewA I).typed).length = 2 ∧
    ((pinAndMkViewA I).fields.map plan).map FieldPlan.shape =
      [.nonrecursive, .nonrecursive] := ⟨rfl, rfl⟩

end Rcic.Declarative.Ann.LR3.AdmittedFamilyExtractor
