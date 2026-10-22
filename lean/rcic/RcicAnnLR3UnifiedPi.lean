import rcic.RcicAnnLR3NeutralCodes
import rcic.RcicAnnLR3NeutralPi

/-!
# Type-indexed finite graphs for the exact-universe Pi joint

The untyped neutral application of `NeutralPi` retains an argument
observation in an arity-one spine. It cannot be an exact universe element,
whose nonbottom observations have the inherited arity-two level tag.
The inhabited control below concerns that particular attempted joint; it
is not a refutation of an admitted source environment or of a model class.

`legalGraph` is a positive, type-indexed correction on the unchanged value
carrier and native application operation. Its rows are sound for every
legal argument. `LegalFiniteDemand` states the precise completeness
condition needed for a general dependent result operation. The graph
construction and its full legal-domain application theorem are supplied.
The condition is supplied for constant result operations and for inherited
native term bodies. In particular, reflection into an exact universe is
constructed for every legal argument, including a concrete inhabited
proof domain and its observationally distinct related arguments.

For a general dependent descriptor family, finite demand of its reflected
results remains an explicit obligation. PER coherence by itself is not
silently substituted for that condition. This file does not supply a
unified descriptor grammar or the source fundamental theorem.
`closure_claim = 0`.
-/

set_option autoImplicit false

namespace Rcic.Declarative.Ann.LR3.UnifiedPi

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER TypedStatements

/-- A finite row is valid at every admitted argument satisfying its
finite demand. The result operation is explicit data, not a selected
representative extracted from a membership proof. -/
def LegalRow (D : Relation) (F : Value → Value)
    (s : List CptI × CptI) : Prop :=
  ∀ x : Value, Member D x → (∀ u ∈ s.1, x u) → F x s.2

/-- All finite tables of sound rows. The existential remains inside the
Prop-valued observation predicate. -/
def legalGraph (D : Relation) (F : Value → Value) : Value := fun c =>
  c = .bot ∨ ∃ g : NeutralPi.Graph, c = .lam g ∧ ∀ s ∈ g, LegalRow D F s

theorem legalGraph_observed (D : Relation) (F : Value → Value) :
    legalGraph D F (.lam []) := Or.inr ⟨[], rfl, by simp⟩

theorem legalGraph_nonbottom (D : Relation) (F : Value → Value) :
    ¬ ValueEq (legalGraph D F) bottom := by
  intro h
  have hb := (h (.lam [])).mp (legalGraph_observed D F)
  cases hb

/-- Completeness of finite demand relative to the complete legal domain.
This is a condition on the result operation, not the desired function
membership theorem. -/
def LegalFiniteDemand (D : Relation) (F : Value → Value) : Prop :=
  ∀ x : Value, Member D x → ∀ c : CptI, F x c →
    ∃ us : List CptI, (∀ u ∈ us, x u) ∧ LegalRow D F (us, c)

theorem applyValue_legalGraph {D : Relation} {F : Value → Value}
    (hbot : ∀ x : Value, Member D x → F x .bot)
    (hfinite : LegalFiniteDemand D F) {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (legalGraph D F) x) (F x) := by
  intro c
  constructor
  · intro hc
    rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
        ⟨head, args, u, hc, hf, ha⟩
    · subst c
      exact hbot x hx
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
        subst c
        exact rows s hs x hx ha
    · rcases hf with hf | ⟨table, he, rows⟩
      · cases hf
      · cases he
  · intro hc
    obtain ⟨us, hus, hrow⟩ := hfinite x hx c hc
    refine Or.inr (Or.inl ⟨[(us, c)], (us, c), rfl, ?_, by simp, hus⟩)
    refine Or.inr ⟨[(us, c)], rfl, ?_⟩
    intro s hs
    simp only [List.mem_singleton] at hs
    subst s
    exact hrow

/-- Binary compatibility applies at all related legal arguments, and may
use two different type-indexed result operations. -/
theorem legalGraph_function_related {D : Relation} (hD : Laws D)
    {C : Value → Relation} {F G : Value → Value}
    (hFbot : ∀ x : Value, Member D x → F x .bot)
    (hGbot : ∀ x : Value, Member D x → G x .bot)
    (hFfinite : LegalFiniteDemand D F) (hGfinite : LegalFiniteDemand D G)
    (hFG : ∀ x y : Value, D x y → C x (F x) (G y)) :
    FunctionPER NeutralPi.applyValue D C (legalGraph D F) (legalGraph D G) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq
    (applyValue_legalGraph hFbot hFfinite (left_member hD hxy))]
  rw [NeutralCodes.valueEq_eq
    (applyValue_legalGraph hGbot hGfinite (right_member hD hxy))]
  exact hFG x y hxy

theorem legalGraph_function_member {D : Relation} (hD : Laws D)
    {C : Value → Relation} {F : Value → Value}
    (hbot : ∀ x : Value, Member D x → F x .bot)
    (hfinite : LegalFiniteDemand D F)
    (hF : ∀ x y : Value, D x y → C x (F x) (F y)) :
    Member (FunctionPER NeutralPi.applyValue D C) (legalGraph D F) :=
  legalGraph_function_related hD hbot hbot hfinite hfinite hF

/-- Empty demands construct completeness for every constant operation,
without an inhabitance or finiteness assumption on its legal domain. -/
theorem constant_legalFiniteDemand (D : Relation) (v : Value) :
    LegalFiniteDemand D (fun _ => v) := by
  intro x _ c hc
  exact ⟨[], by simp, fun _ _ _ => hc⟩

/-- Native bodies have finite demand by the inherited approximation
factorization theorem. This is an actual supply for these operations. -/
theorem native_body_legalFiniteDemand (D : Relation) (ρ : EnvI) (b : Expr Nat) :
    LegalFiniteDemand D (fun x => denI (EnvI.cons x ρ) b) := by
  intro x _ c hc
  obtain ⟨us, hus, hb⟩ := approxI_factor hc 0
  refine ⟨us, hus, ?_⟩
  intro y _ hy
  apply approxI_mono_env (ρ := EnvI.update (EnvI.cons x ρ) 0 (demand us))
    (ρ' := EnvI.cons y ρ) ?_ hb
  intro i u hu
  cases i with
  | zero =>
      have hum : u ∈ us := by simpa [EnvI.update, demand] using hu
      exact hy u hum
  | succ i => simpa [EnvI.update, EnvI.cons] using hu

theorem native_body_graph_application (D : Relation) (ρ : EnvI) (b : Expr Nat)
    {x : Value} (hx : Member D x) :
    ValueEq (NeutralPi.applyValue
      (legalGraph D (fun y => denI (EnvI.cons y ρ) b)) x)
      (denI (EnvI.cons x ρ) b) :=
  applyValue_legalGraph (fun y _ => ApproxI.bot (EnvI.cons y ρ) b)
    (native_body_legalFiniteDemand D ρ b) hx

/-- Every native value application has finite demand in its argument.
The witnesses are the original row demand, one spine argument, or the
empty demand for bottom. No function membership is assumed. -/
theorem application_legalFiniteDemand (D : Relation) (f : Value) :
    LegalFiniteDemand D (NeutralPi.applyValue f) := by
  intro x _ c hc
  rcases hc with hc | ⟨g, s, hc, hf, hs, ha⟩ |
      ⟨head, args, u, hc, hf, ha⟩
  · exact ⟨[], by simp, fun _ _ _ => Or.inl hc⟩
  · exact ⟨s.1, ha,
      fun _ _ hy => Or.inr (Or.inl ⟨g, s, hc, hf, hs, hy⟩)⟩
  · refine ⟨[u], ?_, ?_⟩
    · intro v hv
      simp only [List.mem_singleton] at hv
      subst v
      exact ha
    · intro y _ hy
      exact Or.inr (Or.inr ⟨head, args, u, hc, hf, hy u (by simp)⟩)

/-- The complete graph of a value's native application on its legal
domain. It contains all valid finite rows, not a chosen approximation. -/
def etaGraph (D : Relation) (f : Value) : Value :=
  legalGraph D (NeutralPi.applyValue f)

theorem etaGraph_application (D : Relation) (f : Value) {x : Value}
    (hx : Member D x) :
    ValueEq (NeutralPi.applyValue (etaGraph D f) x)
      (NeutralPi.applyValue f x) :=
  applyValue_legalGraph (fun _ _ => Or.inl rfl)
    (application_legalFiniteDemand D f) hx

/-- Native application equality supplies eta in the complete function
PER. Source lifting and the source eta arm are separate obligations. -/
theorem etaGraph_related {D : Relation} (hD : Laws D)
    {C : Value → Relation} {f : Value}
    (hf : Member (FunctionPER NeutralPi.applyValue D C) f) :
    FunctionPER NeutralPi.applyValue D C (etaGraph D f) f := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (etaGraph_application D f (left_member hD hxy))]
  exact hf x y hxy

theorem etaGraph_member {D : Relation} (hD : Laws D)
    {C : Value → Relation} {f : Value}
    (hf : Member (FunctionPER NeutralPi.applyValue D C) f) :
    Member (FunctionPER NeutralPi.applyValue D C) (etaGraph D f) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (etaGraph_application D f (left_member hD hxy)),
    NeutralCodes.valueEq_eq (etaGraph_application D f (right_member hD hxy))]
  exact hf x y hxy

theorem etaGraphs_related {D : Relation} (hD : Laws D)
    {C : Value → Relation} {f g : Value}
    (hfg : FunctionPER NeutralPi.applyValue D C f g) :
    FunctionPER NeutralPi.applyValue D C (etaGraph D f) (etaGraph D g) := by
  intro x y hxy
  rw [NeutralCodes.valueEq_eq (etaGraph_application D f (left_member hD hxy)),
    NeutralCodes.valueEq_eq (etaGraph_application D g (right_member hD hxy))]
  exact hfg x y hxy

/-- A canonical raw graph for a constant result, valid on every raw
argument. It does not carry a proof of function membership as data. -/
def constantGraph (v : Value) : Value :=
  legalGraph (fun _ _ => True) (fun _ => v)

theorem applyValue_constantGraph (v : Value) (hv : v .bot) (x : Value) :
    ValueEq (NeutralPi.applyValue (constantGraph v) x) v :=
  applyValue_legalGraph (fun _ _ => hv)
    (constant_legalFiniteDemand (fun _ _ => True) v) True.intro

theorem constantGraph_function_member (D C : Relation) {v : Value}
    (hbot : v .bot) (hv : Member C v) :
    Member (FunctionPER NeutralPi.applyValue D (fun _ => C)) (constantGraph v) := by
  intro x y _
  rw [NeutralCodes.valueEq_eq (applyValue_constantGraph v hbot x),
    NeutralCodes.valueEq_eq (applyValue_constantGraph v hbot y)]
  exact hv

theorem reflectDescriptor_bot (d : NeutralCodes.Descriptor) (name : Nat) :
    NeutralCodes.reflectDescriptor d name .bot := by
  cases d with
  | neutralType k other => exact ApproxI.bot EnvI.bot (.const name [])
  | proof P => exact ApproxI.bot EnvI.bot (.const name [])
  | univ k => exact Or.inl rfl

/-- Type-indexed dependent reflection. Completeness of finite demand is
deliberately an explicit premise of its general membership theorem. -/
def descriptorGraph (D : Relation) (B : Value → NeutralCodes.Descriptor)
    (name : Nat) : Value :=
  legalGraph D (fun x => NeutralCodes.reflectDescriptor (B x) name)

theorem descriptorGraph_member {D : Relation} (hD : Laws D)
    (B : Value → NeutralCodes.Descriptor)
    (hB : FamilyCoherent D (fun x => NeutralCodes.El (B x)))
    (name : Nat)
    (hfinite : LegalFiniteDemand D
      (fun x => NeutralCodes.reflectDescriptor (B x) name)) :
    Member (FunctionPER NeutralPi.applyValue D (fun x => NeutralCodes.El (B x)))
      (descriptorGraph D B name) := by
  change Member (FunctionPER NeutralPi.applyValue D (fun x => NeutralCodes.El (B x)))
    (legalGraph D (fun x => NeutralCodes.reflectDescriptor (B x) name))
  apply legalGraph_function_member (C := fun x => NeutralCodes.El (B x))
    (F := fun x => NeutralCodes.reflectDescriptor (B x) name) hD
    (fun x _ => reflectDescriptor_bot (B x) name) hfinite
  intro x y hxy
  exact NeutralCodes.reflectDescriptor_related_of_same (hB x y hxy) name

/-- Exact universe reflection returns a tagged neutral type code. The
same operation is valid on every raw argument and hence on the entire
legal domain of every domain PER. -/
def universeGraph (k : Option Nat) (name : Nat) : Value :=
  constantGraph (NeutralCodes.reify (.neutralType k name))

theorem universeGraph_application (k : Option Nat) (name : Nat) (x : Value) :
    ValueEq (NeutralPi.applyValue (universeGraph k name) x)
      (NeutralCodes.reify (.neutralType k name)) :=
  applyValue_constantGraph _ (Or.inl rfl) x

theorem universeGraph_function_member (D : Relation) (k : Option Nat) (name : Nat) :
    Member (FunctionPER NeutralPi.applyValue D
      (fun _ => NeutralCodes.UniversePER k)) (universeGraph k name) :=
  constantGraph_function_member D (NeutralCodes.UniversePER k) (Or.inl rfl)
    (NeutralCodes.reflectDescriptor_member (.univ k) name)

theorem universeGraph_functions_related (D : Relation) (k : Option Nat) (r s : Nat) :
    FunctionPER NeutralPi.applyValue D (fun _ => NeutralCodes.UniversePER k)
      (universeGraph k r) (universeGraph k s) := by
  intro x y _
  rw [NeutralCodes.valueEq_eq (universeGraph_application k r x),
    NeutralCodes.valueEq_eq (universeGraph_application k s y)]
  exact ⟨.neutralType k r, .neutralType k s, rfl, rfl,
    ValueEq.refl _, ValueEq.refl _⟩

theorem unarySpine_not_sort_member (r : Nat) (k : Option Nat)
    {x : Value} {a : CptI} (hx : x a) :
    ¬ SortMember k (NeutralFamily.unarySpine r x) := by
  intro hs
  have ht := hs _ (NeutralFamily.unarySpine_observed r hx)
  cases ht

theorem unarySpine_not_universe_member (r : Nat) (k : Option Nat)
    {x : Value} {a : CptI} (hx : x a) :
    ¬ Member (NeutralCodes.UniversePER k) (NeutralFamily.unarySpine r x) := by
  intro h
  exact unarySpine_not_sort_member r k hx
    (NeutralCodes.universe_elim (NeutralCodes.code_universe k) h).1

theorem raw_atom_not_universe_function {D : Relation} {x : Value} {a : CptI}
    (hx : Member D x) (ha : x a) (k : Option Nat) (r : Nat) :
    ¬ Member (FunctionPER NeutralPi.applyValue D
      (fun _ => NeutralCodes.UniversePER k)) (NeutralPER.neutralAtom r) := by
  intro h
  have hu := h x x hx
  rw [NeutralCodes.valueEq_eq (NeutralPi.applyValue_atom r x)] at hu
  exact unarySpine_not_universe_member r k ha hu

theorem raw_graph_not_universe_function {D : Relation} {x : Value} {a : CptI}
    (hx : Member D x) (ha : x a) (k : Option Nat) (r : Nat) :
    ¬ Member (FunctionPER NeutralPi.applyValue D
      (fun _ => NeutralCodes.UniversePER k)) (NeutralPi.reflectGraph r) := by
  intro h
  have hu := h x x hx
  rw [NeutralCodes.valueEq_eq (NeutralPi.applyValue_graph r x)] at hu
  exact unarySpine_not_universe_member r k ha hu

/-- Extending this exact universe with the old untagged neutral edges
changes its carrier. Thus equality of the two fibres is unavailable at
this inhabited index. The theorem makes no source admission claim. -/
theorem extended_not_universe {D : Relation} {x : Value} {a : CptI}
    (hx : Member D x) (ha : x a) (k : Option Nat) (r : Nat) :
    ¬ Same (NeutralPi.Extended D (fun _ => NeutralCodes.UniversePER k) x)
      (NeutralCodes.UniversePER k) := by
  intro hs
  have he : NeutralPi.Extended D (fun _ => NeutralCodes.UniversePER k) x
      (NeutralFamily.unarySpine r x) (NeutralFamily.unarySpine r x) :=
    NeutralPi.extended_neutral ⟨r, x, x, hx, hx, ValueEq.refl _, ValueEq.refl _⟩
  exact unarySpine_not_universe_member r k ha ((hs _ _).mp he)

namespace ExactUniverseControl

def domain : Relation := NeutralCodes.El (.proof True)

theorem domain_code : NeutralCodes.Code (some 0)
    (NeutralCodes.reify (.proof True)) domain := NeutralCodes.code (.proof True)

theorem domain_laws : Laws domain := NeutralCodes.el_laws (.proof True)

theorem canonical_member : Member domain (unitValue EnvI.bot) :=
  NeutralPER.unit_member_of_truth NeutralCodes.Neutral True.intro

theorem neutral_member : Member domain (NeutralPER.neutralAtom 501) :=
  NeutralPER.neutral_member NeutralCodes.Neutral True ⟨501, ValueEq.refl _⟩

theorem legal_pair : domain (unitValue EnvI.bot) (NeutralPER.neutralAtom 501) :=
  NeutralPER.proofPER_irrelevant canonical_member neutral_member

theorem exact_fibre_code (k : Option Nat) :
    NeutralCodes.Code (k.map Nat.succ) (universeValue k)
      (NeutralCodes.UniversePER k) := NeutralCodes.code_universe k

/-- The repaired graph works on the complete domain, and in particular
on two related legal arguments with different observations. Both the
domain and codomain have actual codes in the inherited code algebra. -/
theorem supplied (k : Option Nat) :
    Laws (FunctionPER NeutralPi.applyValue domain
      (fun _ => NeutralCodes.UniversePER k)) ∧
    Member (FunctionPER NeutralPi.applyValue domain
      (fun _ => NeutralCodes.UniversePER k)) (universeGraph k 502) ∧
    NeutralCodes.UniversePER k
      (NeutralPi.applyValue (universeGraph k 502) (unitValue EnvI.bot))
      (NeutralPi.applyValue (universeGraph k 502) (NeutralPER.neutralAtom 501)) ∧
    ¬ ValueEq (NeutralPER.neutralAtom 501) (unitValue EnvI.bot) :=
  ⟨functionPER_laws NeutralPi.applyValue domain_laws
      (fun _ _ => NeutralCodes.universePER_laws k) (fun _ _ _ _ _ => Iff.rfl),
    universeGraph_function_member domain k 502,
    universeGraph_function_member domain k 502 _ _ legal_pair,
    NeutralPER.neutralAtom_not_unit 501⟩

theorem old_graph_failure (k : Option Nat) :
    ¬ Member (FunctionPER NeutralPi.applyValue domain
      (fun _ => NeutralCodes.UniversePER k)) (NeutralPi.reflectGraph 502) :=
  raw_graph_not_universe_function canonical_member (unit_observed EnvI.bot) k 502

theorem old_extension_failure (k : Option Nat) :
    ¬ Same (NeutralPi.Extended domain (fun _ => NeutralCodes.UniversePER k)
      (unitValue EnvI.bot)) (NeutralCodes.UniversePER k) :=
  extended_not_universe canonical_member (unit_observed EnvI.bot) k 502

end ExactUniverseControl

end Rcic.Declarative.Ann.LR3.UnifiedPi
