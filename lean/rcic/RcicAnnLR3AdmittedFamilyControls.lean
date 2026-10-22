import rcic.RcicAnnLR3AdmittedFamilyExtractor
import rcic.RcicAnnAccFrecPin

/-!
# Inhabited functional-field extraction and the raw-label interface test

The functional controls compose the existing W-shaped and Acc-shaped
`EnvWfA.group` admissions. Their fields are `frec`, including the Acc
field's dependent second inner binder. The extractor retains every typed
inner domain, the index telescope, and the recursive tail indices.

The second control concerns one specific proposed adapter: putting raw
nonrecursive field values into `Signature.Rule`. Existing `Bisim.node`
requires equal rules, whereas a field PER can relate distinct proof values.
The family admission, a genuine proof candidate, both field memberships,
the related pair, and both legal trees are supplied. This refutes that
raw-label adapter's congruence law; it does not refute an admitted family,
a relational telescope, or a quotient of constructor labels.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.AdmittedFamilyControls

open Rcic.Declarative AdmittedFamilyExtractor

namespace Functional

/-- The existing W-shaped admission, with its inner domain retained. -/
theorem frec_domain_task (I : IotaIfaceA) :
    (domains (pinFrecNodeViewA I).typed).map (fun d => (d.context, d.type, d.level)) =
      [([], .sort .zero, .succ .zero)] := rfl

theorem frec_catalog_control (I : IotaIfaceA) :
    (catalog (pinFrecGroupWfA I)).map SourceGroup.ref = [10] ∧
    ((catalog (pinFrecGroupWfA I)).map fun g => g.constructors.length) = [1] := ⟨rfl, rfl⟩

/-- The actual Acc-shaped group has a dependent second inner binder.
The preceding nonrecursive field and both inner domains are all retained. -/
theorem acc_domain_tasks (I : IotaIfaceA) :
    (domains (pinAccIntroViewA I).typed).map (fun d => (d.context, d.type, d.level)) =
      [([], .sort .zero, .succ .zero),
       ([.assumption (.sort .zero)], .sort .zero, .succ .zero),
       ([.assumption (.sort .zero), .assumption (.sort .zero)], pinAccGuardA, .zero)] := rfl

theorem acc_plan_retains_dependent_inner :
    plan pinAccFieldA =
      .functional (.sort .zero, .succ .zero) [(pinAccGuardA, .zero)] [.bvar 1] := rfl

theorem acc_catalog_control (I : IotaIfaceA) :
    (catalog (pinAccGroupWfA I)).map SourceGroup.ref = [10] ∧
    ((catalog (pinAccGroupWfA I)).map fun g => g.view.indices.length) = [1] ∧
    ((catalog (pinAccGroupWfA I)).map fun g => g.view.params.length) = [0] := ⟨rfl, rfl, rfl⟩

theorem inhabited_control :
    Nonempty (EnvWfA noIotaA pinFrecGroupEnvA) ∧
    (domains (pinFrecNodeViewA noIotaA).typed).length = 1 ∧
    Nonempty (EnvWfA noIotaA pinAccGroupEnvA) ∧
    (domains (pinAccIntroViewA noIotaA).typed).length = 3 ∧
    ctorShapesA 10 pinAccFamA.nparamsA (pinAccIntroA.normA.getD pinAccIntroA.mtypeA) =
      some [.nonrecursive, .recursive 2] :=
  ⟨⟨pinFrecGroupWfA noIotaA⟩, rfl, ⟨pinAccGroupWfA noIotaA⟩, rfl, rfl⟩

end Functional

namespace RawLabels

open UnitModel TypedPER TypedInductive NeutralDataFamily

/-- One constructor with its two raw proof fields in its rule label. -/
def signature : Signature Unit where
  Rule := fun _ => Value × Value
  Premise := fun _ _ => Empty
  child := fun _ _ p => nomatch p

def node (x y : Value) : Tree signature (fun _ => Nat) () :=
  .node () (x, y) (fun p => nomatch p)

def leafRel (_ : Unit) (a b : Nat) : Prop := a = b

abbrev candidate : Relation := NeutralCodes.El (.proof False)
abbrev x : Value := NeutralPER.neutralAtom 0
abbrev y : Value := NeutralPER.neutralAtom 1

theorem candidate_code :
    NeutralCodes.Code (some 0) (NeutralCodes.proofCodeValue False) candidate :=
  NeutralCodes.code (.proof False)

theorem x_member : Member candidate x := NeutralCodes.reflectDescriptor_member (.proof False) 0
theorem y_member : Member candidate y := NeutralCodes.reflectDescriptor_member (.proof False) 1

theorem fields_related : candidate x y ∧ candidate x x :=
  ⟨NeutralPER.proofPER_irrelevant x_member y_member, x_member⟩

theorem node_legal (a b : Value) : Bisim signature (fun _ => Nat) leafRel (node a b) (node a b) :=
  bisim_refl (fun _ _ => rfl) _

theorem raw_label_not_related :
    ¬ Bisim signature (fun _ => Nat) leafRel (node x x) (node y x) := by
  intro h
  have labels := bisim_node_labels h
  have values : x = y := congrArg Prod.fst labels
  have names : 0 = 1 := InductiveFamily.NatCode.atom_injective
    (show ValueEq x y by rw [values]; exact ValueEq.refl _)
  cases names

/-- The exact forward field-congruence property needed by this raw-label
adapter fails at two related, self-related values of an actual candidate. -/
theorem raw_label_congruence_refuted :
    ¬ (∀ a b c d : Value, candidate a c → candidate b d →
      Bisim signature (fun _ => Nat) leafRel (node a b) (node c d)) := by
  intro h
  exact raw_label_not_related (h x x y x fields_related.1 fields_related.2)

theorem inhabited_adapter_boundary :
    Nonempty (EnvWfA (iotaIfaceA pinAndEnvA) pinAndEnvA) ∧
    (pinAndMkViewA (iotaIfaceA pinAndEnvA)).fields =
      [.plain (.bvar 1) .zero, .plain (.bvar 1) .zero] ∧
    NeutralCodes.Code (some 0) (NeutralCodes.proofCodeValue False) candidate ∧
    Laws candidate ∧ Member candidate x ∧ Member candidate y ∧
    candidate x y ∧ candidate x x ∧
    Bisim signature (fun _ => Nat) leafRel (node x x) (node x x) ∧
    Bisim signature (fun _ => Nat) leafRel (node y x) (node y x) ∧
    ¬ Bisim signature (fun _ => Nat) leafRel (node x x) (node y x) :=
  ⟨⟨pinAnd_wf⟩, rfl, candidate_code, NeutralCodes.code_lawful candidate_code,
    x_member, y_member, fields_related.1, fields_related.2, node_legal x x,
    node_legal y x, raw_label_not_related⟩

end RawLabels

end Rcic.Declarative.Ann.LR3.AdmittedFamilyControls
