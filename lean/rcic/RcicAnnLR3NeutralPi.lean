import rcic.RcicAnnLR3NeutralFamily
import rcic.RcicAnnLR3NeutralK

/-!
# Constructed neutral functions on the native value carrier

`applyValue` is the native finite-graph and neutral-spine application
operation. Its equation with `denI` follows from the existing application
constructors and their inversion lemma. `reflectGraph` contains every
finite graph of a neutral application; its application agrees with the
actual neutral constant on every argument value, without a normalization
or bottom-completeness premise.

For a domain PER `D`, the dependent codomain extension adds same-head
neutral-application edges along each `D` class and takes nonempty finite
PER closure. Its laws, index coherence, and reflection into the complete
legal-domain function PER are proved below. Reflection membership is not
an input field. The final adapter identifies the precise edge-inclusion
obligation for using a separately chosen codomain interpretation instead.

This constructs a local dependent-function algebra. It does not identify
the constructed family with a global code interpreter, supply source
substitution or all 28 source contracts, or supply `NeutralSupport` for a
complete model. Only forward inclusion into finite PER completion is
used; no converse K condition is needed. `closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.NeutralPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

abbrev Graph := List (List CptI × CptI)

/-- Exactly the three native application observation clauses. -/
def applyValue (f x : Value) : Value := fun c =>
  c = .bot ∨
    (∃ (g : Graph) (s : List CptI × CptI),
      c = s.2 ∧ f (.lam g) ∧ s ∈ g ∧ ∀ u ∈ s.1, x u) ∨
    (∃ (r : Nat) (args : List CptI) (u : CptI),
      c = .spine r (args ++ [u]) ∧ f (.spine r args) ∧ x u)

theorem applyValue_denI (ρ : EnvI) (f a : Expr Nat) :
    ValueEq (applyValue (denI ρ f) (denI ρ a)) (denI ρ (.app f a)) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ | ⟨r, args, u, hc, hf, ha⟩
    · subst c
      exact ApproxI.bot _ _
    · subst c
      exact ApproxI.app hf hs ha
    · subst c
      exact ApproxI.appSpine hf ha
  · exact approxI_app_inv

theorem applyValue_mono {f g x y : Value}
    (hf : ∀ c, f c → g c) (hx : ∀ c, x c → y c) :
    ∀ c, applyValue f x c → applyValue g y c := by
  intro c hc
  rcases hc with hc | ⟨table, s, hc, ht, hs, ha⟩ |
      ⟨r, args, u, hc, ht, ha⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨table, s, hc, hf _ ht, hs, fun u hu => hx u (ha u hu)⟩)
  · exact Or.inr (Or.inr ⟨r, args, u, hc, hf _ ht, hx _ ha⟩)

theorem applyValue_congr {f g x y : Value}
    (hf : ValueEq f g) (hx : ValueEq x y) :
    ValueEq (applyValue f x) (applyValue g y) := by
  intro c
  exact ⟨applyValue_mono (fun d => (hf d).mp) (fun d => (hx d).mp) c,
    applyValue_mono (fun d => (hf d).mpr) (fun d => (hx d).mpr) c⟩

/-- Applying the actual constant value retains every argument observation. -/
theorem applyValue_atom (r : Nat) (x : Value) :
    ValueEq (applyValue (NeutralPER.neutralAtom r) x)
      (NeutralFamily.unarySpine r x) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
        ⟨head, args, u, hc, hf, ha⟩
    · exact Or.inl hc
    · rcases approxI_const_inv hf with h | h
      · cases h
      · cases h
    · rcases approxI_const_inv hf with h | h
      · cases h
      · cases h
        exact Or.inr ⟨u, ha, hc⟩
  · intro hc
    rcases hc with hc | ⟨u, hu, hc⟩
    · exact Or.inl hc
    · exact Or.inr (Or.inr ⟨r, [], u, hc, NeutralPER.neutralAtom_observed r, hu⟩)

/-- A graph row either produces bottom or records one demanded argument
observation in the neutral spine. -/
def GraphRow (r : Nat) (s : List CptI × CptI) : Prop :=
  s.2 = .bot ∨ ∃ u : CptI, u ∈ s.1 ∧ s.2 = .spine r [u]

/-- The whole finite graph, not a selected finite approximation. -/
def reflectGraph (r : Nat) : Value := fun c =>
  c = .bot ∨ ∃ g : Graph, c = .lam g ∧ ∀ s ∈ g, GraphRow r s

theorem reflectGraph_observed (r : Nat) : reflectGraph r (.lam []) :=
  Or.inr ⟨[], rfl, by simp⟩

theorem reflectGraph_nonbottom (r : Nat) : ¬ ValueEq (reflectGraph r) bottom := by
  intro h
  have hb := (h (.lam [])).mp (reflectGraph_observed r)
  cases hb

/-- Every raw argument is covered. Singleton rows prove the reverse
inclusion, while arbitrary finite tables prove the forward inclusion. -/
theorem applyValue_graph (r : Nat) (x : Value) :
    ValueEq (applyValue (reflectGraph r) x) (NeutralFamily.unarySpine r x) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
        ⟨head, args, u, hc, hf, ha⟩
    · exact Or.inl hc
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
        rcases rows s hs with hb | ⟨u, hu, hout⟩
        · exact Or.inl (hc.trans hb)
        · exact Or.inr ⟨u, ha u hu, hc.trans hout⟩
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
  · intro hc
    rcases hc with hc | ⟨u, hu, hc⟩
    · exact Or.inl hc
    · refine Or.inr (Or.inl ⟨[([u], .spine r [u])],
        ([u], .spine r [u]), hc, ?_, by simp, ?_⟩)
      · refine Or.inr ⟨[([u], .spine r [u])], rfl, ?_⟩
        intro s hs
        simp only [List.mem_singleton] at hs
        subst s
        exact Or.inr ⟨u, by simp, rfl⟩
      · intro a ha
        simp only [List.mem_singleton] at ha
        subst a
        exact hu

theorem graph_atom_apply (r : Nat) (x : Value) :
    ValueEq (applyValue (reflectGraph r) x)
      (applyValue (NeutralPER.neutralAtom r) x) :=
  (applyValue_graph r x).trans (applyValue_atom r x).symm

/-- Applications with the same neutral head and arguments from the
current legal domain class. Distinct data neutral heads are not declared
equal by this generator. -/
def NeutralEdge (D : Relation) (i : Value) (u v : Value) : Prop :=
  ∃ (r : Nat) (x y : Value),
    D i x ∧ D i y ∧
      ValueEq u (NeutralFamily.unarySpine r x) ∧
      ValueEq v (NeutralFamily.unarySpine r y)

theorem neutralEdge_index {D : Relation} (hD : Laws D)
    {i j : Value} (hij : D i j) : Same (NeutralEdge D i) (NeutralEdge D j) := by
  intro u v
  constructor
  · rintro ⟨r, x, y, hix, hiy, hu, hv⟩
    exact ⟨r, x, y, hD.trans (hD.symm hij) hix,
      hD.trans (hD.symm hij) hiy, hu, hv⟩
  · rintro ⟨r, x, y, hjx, hjy, hu, hv⟩
    exact ⟨r, x, y, hD.trans hij hjx, hD.trans hij hjy, hu, hv⟩

theorem neutralEdge_domain {D E : Relation} (hDE : Same D E) (i : Value) :
    Same (NeutralEdge D i) (NeutralEdge E i) := by
  intro u v
  constructor
  · rintro ⟨r, x, y, hix, hiy, hu, hv⟩
    exact ⟨r, x, y, (hDE i x).mp hix, (hDE i y).mp hiy, hu, hv⟩
  · rintro ⟨r, x, y, hix, hiy, hu, hv⟩
    exact ⟨r, x, y, (hDE i x).mpr hix, (hDE i y).mpr hiy, hu, hv⟩

def CodomainSeed (D : Relation) (C : Value → Relation) (i : Value) : Relation :=
  fun u v => C i u v ∨ NeutralEdge D i u v

/-- A positive, explicit codomain extension; no function membership
certificate is stored in its definition. -/
def Extended (D : Relation) (C : Value → Relation) (i : Value) : Relation :=
  NeutralK.Path (CodomainSeed D C i)

theorem extended_laws (D : Relation) (C : Value → Relation) (i : Value) :
    Laws (Extended D C i) := NeutralK.path_typed_laws _

theorem extended_core {D : Relation} {C : Value → Relation} {i u v : Value}
    (h : C i u v) : Extended D C i u v := .forward (Or.inl h)

theorem extended_neutral {D : Relation} {C : Value → Relation} {i u v : Value}
    (h : NeutralEdge D i u v) : Extended D C i u v := .forward (Or.inr h)

theorem extended_coherent {D : Relation} (hD : Laws D)
    {C : Value → Relation} (hc : FamilyCoherent D C) :
    FamilyCoherent D (Extended D C) := by
  intro i j hij
  exact NeutralK.path_same (fun u v =>
    or_congr (hc i j hij u v) (neutralEdge_index hD hij u v))

/-- Extensional replacement of the domain and codomain data commutes with
the generated extension, supplying a concrete family transport law. -/
theorem extended_parameters {D E : Relation} (hDE : Same D E)
    {C F : Value → Relation} (hCF : ∀ i, Same (C i) (F i)) (i : Value) :
    Same (Extended D C i) (Extended E F i) :=
  NeutralK.path_same (fun u v =>
    or_congr (hCF i u v) (neutralEdge_domain hDE i u v))

theorem function_laws {D : Relation} (hD : Laws D)
    {C : Value → Relation} (hc : FamilyCoherent D C) :
    Laws (FunctionPER applyValue D (Extended D C)) :=
  functionPER_laws applyValue hD (fun i _ => extended_laws D C i)
    (extended_coherent hD hc)

/-- Full legal-domain reflection of the actual native neutral constant. -/
theorem atom_function_member {D : Relation} (hD : Laws D)
    (C : Value → Relation) (r : Nat) :
    Member (FunctionPER applyValue D (Extended D C)) (NeutralPER.neutralAtom r) := by
  intro x y hxy
  exact extended_neutral ⟨r, x, y, left_member hD hxy, hxy,
    applyValue_atom r x, applyValue_atom r y⟩

/-- Full legal-domain reflection of the entire finite graph. -/
theorem graph_function_member {D : Relation} (hD : Laws D)
    (C : Value → Relation) (r : Nat) :
    Member (FunctionPER applyValue D (Extended D C)) (reflectGraph r) := by
  intro x y hxy
  exact extended_neutral ⟨r, x, y, left_member hD hxy, hxy,
    applyValue_graph r x, applyValue_graph r y⟩

theorem atom_graph_related {D : Relation} (hD : Laws D)
    (C : Value → Relation) (r : Nat) :
    FunctionPER applyValue D (Extended D C)
      (NeutralPER.neutralAtom r) (reflectGraph r) := by
  intro x y hxy
  exact extended_neutral ⟨r, x, y, left_member hD hxy, hxy,
    applyValue_atom r x, applyValue_graph r y⟩

/-- Explicit laws and inhabitants for the constructed family. -/
theorem function_reflection_supplied {D : Relation} (hD : Laws D)
    {C : Value → Relation} (hc : FamilyCoherent D C) (r : Nat) :
    Laws (FunctionPER applyValue D (Extended D C)) ∧
    Member (FunctionPER applyValue D (Extended D C)) (NeutralPER.neutralAtom r) ∧
    Member (FunctionPER applyValue D (Extended D C)) (reflectGraph r) ∧
    FunctionPER applyValue D (Extended D C)
      (NeutralPER.neutralAtom r) (reflectGraph r) :=
  ⟨function_laws hD hc, atom_function_member hD C r,
    graph_function_member hD C r, atom_graph_related hD C r⟩

/-- Adapter to a separately chosen codomain. This edge-inclusion premise
is a residual obligation, not a supplied property of a global decoder. -/
theorem graph_member_of_neutral_edges {D : Relation} (hD : Laws D)
    {C : Value → Relation}
    (includeNeutral : ∀ (i u v : Value), NeutralEdge D i u v → C i u v)
    (r : Nat) : Member (FunctionPER applyValue D C) (reflectGraph r) := by
  intro x y hxy
  exact includeNeutral x _ _ ⟨r, x, y, left_member hD hxy, hxy,
    applyValue_graph r x, applyValue_graph r y⟩

/-- At a proof-valued codomain all admitted neutral results join the
canonical proof class, including results with different neutral heads. -/
def NeutralResult (D : Relation) (i : Value) (v : Value) : Prop :=
  ∃ (r : Nat) (x : Value), D i x ∧ ValueEq v (NeutralFamily.unarySpine r x)

theorem neutralResult_index {D : Relation} (hD : Laws D)
    {i j : Value} (hij : D i j) (v : Value) :
    NeutralResult D i v ↔ NeutralResult D j v := by
  constructor
  · rintro ⟨r, x, hix, hv⟩
    exact ⟨r, x, hD.trans (hD.symm hij) hix, hv⟩
  · rintro ⟨r, x, hjx, hv⟩
    exact ⟨r, x, hD.trans hij hjx, hv⟩

def ProofCodomain (D : Relation) (truth : Value → Prop) (i : Value) : Relation :=
  NeutralPER.ProofPER (NeutralResult D i) (truth i)

theorem proofCodomain_laws (D : Relation) (truth : Value → Prop) (i : Value) :
    Laws (ProofCodomain D truth i) := NeutralPER.proofPER_laws _ _

theorem proofCodomain_coherent {D : Relation} (hD : Laws D)
    {truth : Value → Prop} (ht : ∀ i j, D i j → (truth i ↔ truth j)) :
    FamilyCoherent D (ProofCodomain D truth) := by
  intro i j hij
  exact NeutralPER.proofPER_same (ht i j hij) (neutralResult_index hD hij)

theorem proof_function_laws {D : Relation} (hD : Laws D)
    {truth : Value → Prop} (ht : ∀ i j, D i j → (truth i ↔ truth j)) :
    Laws (FunctionPER applyValue D (ProofCodomain D truth)) :=
  functionPER_laws applyValue hD (fun i _ => proofCodomain_laws D truth i)
    (proofCodomain_coherent hD ht)

theorem atom_proof_function_member {D : Relation} (hD : Laws D)
    (truth : Value → Prop) (r : Nat) :
    Member (FunctionPER applyValue D (ProofCodomain D truth))
      (NeutralPER.neutralAtom r) := by
  intro x y hxy
  exact ⟨Or.inr ⟨r, x, left_member hD hxy, applyValue_atom r x⟩,
    Or.inr ⟨r, y, hxy, applyValue_atom r y⟩⟩

theorem graph_proof_function_member {D : Relation} (hD : Laws D)
    (truth : Value → Prop) (r : Nat) :
    Member (FunctionPER applyValue D (ProofCodomain D truth)) (reflectGraph r) := by
  intro x y hxy
  exact ⟨Or.inr ⟨r, x, left_member hD hxy, applyValue_graph r x⟩,
    Or.inr ⟨r, y, hxy, applyValue_graph r y⟩⟩

/-- Pointwise proof irrelevance collapses every pair of function members,
including members supplied by neutral reflection. -/
theorem proof_function_irrelevant {D : Relation} {truth : Value → Prop}
    {f g : Value}
    (hf : Member (FunctionPER applyValue D (ProofCodomain D truth)) f)
    (hg : Member (FunctionPER applyValue D (ProofCodomain D truth)) g) :
    FunctionPER applyValue D (ProofCodomain D truth) f g := by
  intro x y hxy
  exact ⟨(hf x y hxy).1, (hg x y hxy).2⟩

theorem proof_reflections_related {D : Relation} (hD : Laws D)
    (truth : Value → Prop) (r s : Nat) :
    FunctionPER applyValue D (ProofCodomain D truth)
      (NeutralPER.neutralAtom r) (reflectGraph s) :=
  proof_function_irrelevant (atom_proof_function_member hD truth r)
    (graph_proof_function_member hD truth s)

namespace InhabitedControl

/-- The domain admits a canonical proof and an observationally distinct
neutral proof in the same proof-irrelevant class. -/
def domain : Relation := NeutralPER.ProofPER (NeutralPER.AtomNeutral 401) True

theorem domain_laws : Laws domain := NeutralPER.proofPER_laws _ _

theorem canonical_member : Member domain (unitValue EnvI.bot) :=
  NeutralPER.unit_member_of_truth _ True.intro

theorem neutral_member : Member domain (NeutralPER.neutralAtom 401) :=
  NeutralPER.neutral_member _ _ (NeutralPER.neutralAtom_is_neutral 401)

theorem legal_pair : domain (unitValue EnvI.bot) (NeutralPER.neutralAtom 401) :=
  NeutralPER.proofPER_irrelevant canonical_member neutral_member

def core (_i : Value) : Relation := fun _ _ => False

theorem core_coherent : FamilyCoherent domain core :=
  fun _ _ _ _ _ => Iff.rfl

theorem supplied :
    Laws (FunctionPER applyValue domain (Extended domain core)) ∧
    Member (FunctionPER applyValue domain (Extended domain core)) (reflectGraph 402) ∧
    Extended domain core (unitValue EnvI.bot)
      (applyValue (reflectGraph 402) (unitValue EnvI.bot))
      (applyValue (reflectGraph 402) (NeutralPER.neutralAtom 401)) ∧
    ¬ ValueEq (NeutralPER.neutralAtom 401) (unitValue EnvI.bot) :=
  ⟨function_laws domain_laws core_coherent,
    graph_function_member domain_laws core 402,
    graph_function_member domain_laws core 402 _ _ legal_pair,
    NeutralPER.neutralAtom_not_unit 401⟩

end InhabitedControl

end Rcic.Declarative.Ann.LR3.NeutralPi
