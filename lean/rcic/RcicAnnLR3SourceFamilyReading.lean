import rcic.RcicAnnLR3AdmittedFamilyExtractor
import rcic.RcicAnnEqLargeFixture

/-!
# Source-bound family signature metadata

The constructor inventory and every field/index task come from the actual
Type-valued admission catalog. The reader checks the source family head and
its exact parameter/index arity. Its public entry point selects the group
from that catalog, rather than taking a caller-chosen signature or matching
a raw type image.

This certifies source declaration metadata and application shape. It does
not prove that arbitrary application arguments are well typed or construct
their semantic field interpretation. Eq is a proposition; this module does
not apply the positive familyCode producer to Eq. An empty rule fibre at a
particular Eq index is distinct from deleting its source refl constructor.
closure_claim = 0.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.SourceFamilyReading
open Rcic.Declarative
open AdmittedFamilyExtractor

abbrev Constructor {I : IotaIfaceA} (g : SourceGroup I) :=
  Fin g.constructors.length

def constructorAt {I : IotaIfaceA} (g : SourceGroup I) (c : Constructor g) :
    GroupCtorA I g.base g.ref g.member g.view := g.constructors.get c

def constructorRef {I : IotaIfaceA} (g : SourceGroup I) (c : Constructor g) : Nat :=
  (constructorAt g c).ref

def constructorFields {I : IotaIfaceA} (g : SourceGroup I) (c : Constructor g) :
    List FieldPlan := constructorPlans g (constructorAt g c)

def constructorDomainsAt {I : IotaIfaceA} (g : SourceGroup I) (c : Constructor g) :
    List (DomainTask g.base I g.member.arity) :=
  constructorDomains g (constructorAt g c)

def constructorIndicesAt {I : IotaIfaceA} (g : SourceGroup I) (c : Constructor g) :
    List (IndexTask g.base I g.member.arity) :=
  constructorIndices g (constructorAt g c)

theorem constructorFields_source {I : IotaIfaceA} (g : SourceGroup I)
    (c : Constructor g) :
    (constructorFields g c).map FieldPlan.source = (constructorAt g c).view.fields :=
  constructorPlans_lossless g (constructorAt g c)

theorem constructorFields_shape {I : IotaIfaceA} (g : SourceGroup I)
    (c : Constructor g) :
    ctorShapesA g.ref g.member.nparamsA
      ((constructorAt g c).member.normA.getD (constructorAt g c).member.mtypeA) =
      some ((constructorFields g c).map FieldPlan.shape) :=
  normalized_shape_exact g (constructorAt g c)

structure SourceSignature where
  familyRef : Nat
  parameters : List (ExprA × Level)
  indices : List (ExprA × Level)
  constructorRefs : List Nat
  fields : List (List FieldPlan)

def signatureOf {I : IotaIfaceA} (g : SourceGroup I) : SourceSignature where
  familyRef := g.ref
  parameters := g.view.params
  indices := g.view.indices
  constructorRefs := g.constructors.map GroupCtorA.ref
  fields := g.constructors.map (constructorPlans g)

theorem signature_constructor_count {I : IotaIfaceA} (g : SourceGroup I) :
    (signatureOf g).constructorRefs.length = g.constructors.length := by
  simp only [signatureOf, List.length_map]

def headRef : ExprA → Option Nat
  | .const r _ => some r
  | .app f _ => headRef f
  | _ => none

def appArity : ExprA → Nat
  | .app f _ => appArity f + 1
  | _ => 0

theorem headRef_foldAppsA (f : ExprA) (as : List ExprA) :
    headRef (foldAppsA f as) = headRef f := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih (.app f a)

theorem appArity_foldAppsA (f : ExprA) (as : List ExprA) :
    appArity (foldAppsA f as) = appArity f + as.length := by
  induction as generalizing f with
  | nil => simp only [foldAppsA, List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons a as ih =>
      calc
        appArity (foldAppsA f (a :: as)) =
            appArity (foldAppsA (.app f a) as) := rfl
        _ = appArity (.app f a) + as.length := ih _
        _ = appArity f + (a :: as).length := by
          simp only [appArity, List.length_cons]
          omega

def ReadShape {I : IotaIfaceA} (g : SourceGroup I) (e : ExprA) : Prop :=
  headRef e = some g.ref ∧ appArity e = g.view.params.length + g.view.indices.length

instance readShapeDecidable {I : IotaIfaceA} (g : SourceGroup I) (e : ExprA) :
    Decidable (ReadShape g e) :=
  inferInstanceAs (Decidable
    (headRef e = some g.ref ∧ appArity e = g.view.params.length + g.view.indices.length))

structure CatalogReading {I : IotaIfaceA} (gs : List (SourceGroup I)) (e : ExprA) where
  group : SourceGroup I
  inCatalog : group ∈ gs
  shape : ReadShape group e

def CatalogReading.signature {I : IotaIfaceA} {gs : List (SourceGroup I)}
    {e : ExprA} (r : CatalogReading gs e) : SourceSignature := signatureOf r.group

def readCatalog {I : IotaIfaceA} :
    (gs : List (SourceGroup I)) → (e : ExprA) → Option (CatalogReading gs e)
  | [], _ => none
  | g :: gs, e =>
      if h : ReadShape g e then
        some ⟨g, List.mem_cons_self _ _, h⟩
      else
        match readCatalog gs e with
        | none => none
        | some r => some ⟨r.group, List.mem_cons_of_mem _ r.inCatalog, r.shape⟩

def readerOf {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (e : ExprA) : Option (CatalogReading (catalog hE) e) :=
  readCatalog (catalog hE) e

theorem readCatalog_complete {I : IotaIfaceA} (gs : List (SourceGroup I)) (e : ExprA) :
    (∃ g ∈ gs, ReadShape g e) → ∃ r, readCatalog gs e = some r := by
  induction gs with
  | nil =>
      rintro ⟨g, hg, _⟩
      cases hg
  | cons g gs ih =>
      intro h
      by_cases hs : ReadShape g e
      · refine ⟨⟨g, List.mem_cons_self _ _, hs⟩, ?_⟩
        simp only [readCatalog, dif_pos hs]
      · rcases h with ⟨j, hj, hjshape⟩
        have htail : j ∈ gs := by
          rcases List.mem_cons.mp hj with he | ht
          · subst j
            exact (hs hjshape).elim
          · exact ht
        obtain ⟨r, hr⟩ := ih ⟨j, htail, hjshape⟩
        refine ⟨⟨r.group, List.mem_cons_of_mem _ r.inCatalog, r.shape⟩, ?_⟩
        simp only [readCatalog, dif_neg hs, hr]

theorem readCatalog_exists_iff {I : IotaIfaceA}
    (gs : List (SourceGroup I)) (e : ExprA) :
    (∃ r, readCatalog gs e = some r) ↔ ∃ g ∈ gs, ReadShape g e :=
  ⟨fun ⟨r, _⟩ => ⟨r.group, r.inCatalog, r.shape⟩, readCatalog_complete gs e⟩

theorem readerOf_exists_iff {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (e : ExprA) :
    (∃ r, readerOf hE e = some r) ↔ ∃ g ∈ catalog hE, ReadShape g e :=
  readCatalog_exists_iff (catalog hE) e

theorem readerOf_functional {I : IotaIfaceA} {E : ResolvedEnvA}
    (hE : EnvWfA I E) (e : ExprA)
    {r s : CatalogReading (catalog hE) e}
    (hr : readerOf hE e = some r) (hs : readerOf hE e = some s) : r = s :=
  Option.some.inj (hr.symm.trans hs)

theorem source_application_shape {I : IotaIfaceA} (g : SourceGroup I)
    (ls : List Level) (ps is : List ExprA)
    (hp : ps.length = g.view.params.length) (hi : is.length = g.view.indices.length) :
    ReadShape g (foldAppsA (.const g.ref ls) (ps ++ is)) := by
  constructor
  · rw [headRef_foldAppsA]
    rfl
  · rw [appArity_foldAppsA]
    simp only [appArity, Nat.zero_add, List.length_append, hp, hi]

/-- Direct selection from the actual Eq prefix admission. A Nonempty final
admission witness is not eliminated into data. -/
def eqGroup : SourceGroup noIotaA :=
  (catalog EqLargeFixture.prefixWf).get
    ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩

def eqConstructor : Constructor eqGroup :=
  ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩

theorem eq_catalog_singleton : catalog EqLargeFixture.prefixWf = [eqGroup] := rfl

theorem eq_catalog_entry {g : SourceGroup noIotaA}
    (h : g ∈ catalog EqLargeFixture.prefixWf) : g = eqGroup := by
  rw [eq_catalog_singleton] at h
  exact List.mem_singleton.mp h

theorem eq_ref : eqGroup.ref = 63 := rfl

theorem eq_parameter_telescope : eqGroup.view.params =
    [(.sort (.succ .zero), .succ (.succ .zero)), (.bvar 0, .succ .zero)] := rfl

theorem eq_index_telescope : eqGroup.view.indices = [(.bvar 1, .succ .zero)] := rfl

theorem eq_constructor_refs : (signatureOf eqGroup).constructorRefs = [64] := rfl

theorem eq_constructor_fields : constructorFields eqGroup eqConstructor = [] := rfl

theorem eq_constructor_indices :
    (constructorIndicesAt eqGroup eqConstructor).map (fun t => t.arguments) =
      [[.bvar 0]] := rfl

theorem eq_constructor_inventory_nonempty : eqGroup.constructors ≠ [] := by
  intro h
  have hn := congrArg List.length h
  change 1 = 0 at hn
  cases hn

theorem eq_signature_not_empty : (signatureOf eqGroup).constructorRefs ≠ [] := by
  rw [eq_constructor_refs]
  intro h
  cases h

def eqApplication (A a b : ExprA) : ExprA :=
  foldAppsA (.const 63 []) [A, a, b]

theorem eq_application_read (A a b : ExprA) :
    ∃ r, readerOf EqLargeFixture.prefixWf (eqApplication A a b) = some r ∧
      r.signature.constructorRefs = [64] := by
  have h : ReadShape eqGroup (eqApplication A a b) :=
    source_application_shape eqGroup [] [A, a] [b] rfl rfl
  change ∃ r : CatalogReading [eqGroup] (eqApplication A a b),
    readCatalog [eqGroup] (eqApplication A a b) = some r ∧
      r.signature.constructorRefs = [64]
  refine ⟨⟨eqGroup, List.mem_cons_self _ _, h⟩, ?_, rfl⟩
  simp only [readCatalog, dif_pos h]

theorem eq_reading_inventory {e : ExprA}
    (r : CatalogReading (catalog EqLargeFixture.prefixWf) e) :
    r.signature.constructorRefs = [64] := by
  change (signatureOf r.group).constructorRefs = [64]
  rw [eq_catalog_entry r.inCatalog]
  exact eq_constructor_refs

theorem eq_call_head (p : ExprA) :
    headRef (EqLargeFixture.call p) = some 65 := rfl

theorem eq_call_not_shape (p : ExprA) : ¬ ReadShape eqGroup (EqLargeFixture.call p) := by
  intro h
  have hh := h.1
  rw [eq_call_head, eq_ref] at hh
  have hn : (65 : Nat) = 63 := Option.some.inj hh
  omega

theorem eq_call_no_catalog_reading (p : ExprA) :
    ¬ Nonempty (CatalogReading (catalog EqLargeFixture.prefixWf)
      (EqLargeFixture.call p)) := by
  rintro ⟨r⟩
  have hs := r.shape
  rw [eq_catalog_entry r.inCatalog] at hs
  exact eq_call_not_shape p hs

theorem eq_call_rejected (p : ExprA) :
    readerOf EqLargeFixture.prefixWf (EqLargeFixture.call p) = none := by
  change readCatalog [eqGroup] (EqLargeFixture.call p) = none
  simp only [readCatalog, dif_neg (eq_call_not_shape p)]

end Rcic.Declarative.Ann.LR3.SourceFamilyReading
