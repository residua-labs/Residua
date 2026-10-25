import rcic.RcicF3GroupWalk

/-!
# F3 S5a-13: structural facts about admitted groups

- `policyPi_split_eq`: a telescope with a non-Π end determines its domains
  and its end;
- `fieldShapesFuel_length`;
- `TypeFacts`: every member's stored type (and body) is closed and has its
  levels bounded by the member's arity (`typeFacts_of_envWfT`);
- `GroupClass` / `ClassG`: the class of environments `consistent4_G`
  covers (axiom-free; in every group, each field
  family-free or the family applied to the parameter locals and family-free
  indices; under `Prop` large elimination, no field revealed in the result
  indices; each
  constructor's own admission view splitting off the recursor view's
  parameters);
- `BoundG` (defined in `RcicF3BoundDefs`): the level bounds on the derivations the proof uses.

closure_claim = 0.
-/

set_option autoImplicit false

namespace Rcic.F3

open Rcic.Declarative

namespace PSet

theorem expr_not_pi_of_sort (l : Level) : ∀ A B, (Expr.sort l : Expr Nat) ≠ .pi A B := fun _ _ h => Expr.noConfusion h

theorem policyPi_split_eq : (D D' : List (Expr Nat)) → (b b' : Expr Nat) → (∀ A B, b ≠ .pi A B) →
    (∀ A B, b' ≠ .pi A B) → policyPi D b = policyPi D' b' → D = D' ∧ b = b'
  | [], [], _, _, _, _, h => ⟨rfl, h⟩
  | [], A :: D', b, _, hb, _, h => absurd h (hb A _)
  | A :: D, [], _, b', _, hb', h => absurd h.symm (hb' A _)
  | A :: D, A' :: D', b, b', hb, hb', h => by
      have h' : Expr.pi A (policyPi D b) = Expr.pi A' (policyPi D' b') := h
      injection h' with h1 h2
      obtain ⟨hD, hbb⟩ := policyPi_split_eq D D' b b' hb hb' h2
      exact ⟨by rw [h1, hD], hbb⟩

theorem fieldShapesFuel_length (E : ResolvedEnv) (fuel fam nuniv nparams nindices : Nat) :
    (Ts : List (Expr Nat)) → (depth : Nat) → (shapes : List FieldShape) →
    fieldShapesFuel E fuel fam nuniv nparams nindices depth Ts = some shapes → shapes.length = Ts.length
  | [], _, shapes, h => by cases h; rfl
  | T :: Ts, depth, shapes, h => by
      unfold fieldShapesFuel at h
      split at h
      · cases hr : fieldShapesFuel E fuel fam nuniv nparams nindices (depth + 1) Ts with
        | none => rw [hr] at h; cases h
        | some rest =>
            rw [hr] at h
            cases h
            simp [fieldShapesFuel_length E fuel fam nuniv nparams nindices Ts (depth + 1) rest hr]
      · cases h

/-- Every member's stored type and body are closed and level-bounded by its arity. -/
def TypeFacts (E : ResolvedEnv) : Prop :=
  ∀ r m, E.members r = some m → (∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype) ∧
    exprLevelsBounded m.arity m.mtype = true ∧
    ∀ b, m.body = some b → (∀ k, Rcic.Declarative.lift k 1 b = b) ∧ exprLevelsBounded m.arity b = true

theorem typeFacts_extend {E : ResolvedEnv} {r : Nat} {m : CheckedMember} (h : TypeFacts E)
    (hm : (∀ k, Rcic.Declarative.lift k 1 m.mtype = m.mtype) ∧ exprLevelsBounded m.arity m.mtype = true ∧
      ∀ b, m.body = some b → (∀ k, Rcic.Declarative.lift k 1 b = b) ∧ exprLevelsBounded m.arity b = true) :
    TypeFacts (extendEnv E r m) := by
  intro r' m' h'
  by_cases hr : r' = r
  · subst hr; rw [members_extend_eq] at h'; cases h'; exact hm
  · rw [members_extend_ne E r m r' hr] at h'; exact h r' m' h'

theorem typeFacts_groupMembersT {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → TypeFacts E → TypeFacts E'
  | _, _, _, .nil _, h => h
  | _, _, _, .cons _ _ _ _ _ _ hnobody hclT _ hlvlB _ _ _ _ _ _ _ _ hrest, h =>
      typeFacts_groupMembersT hrest (typeFacts_extend h ⟨hclT, hlvlB, fun b hb => by rw [hnobody] at hb; cases hb⟩)

theorem typeFacts_of_envWfT : {E : ResolvedEnv} → EnvWfT E → TypeFacts E
  | _, .empty => fun _ _ h => (Option.noConfusion h)
  | _, .axiom _ _ _ _ hE _ _ hcl hlvl =>
      typeFacts_extend (typeFacts_of_envWfT hE) ⟨hcl, hlvl, fun b hb => by cases hb⟩
  | _, .definition _ _ _ _ _ hE _ _ _ hclA hclv hlvlA hlvlv =>
      typeFacts_extend (typeFacts_of_envWfT hE) ⟨hclA, hlvlA, fun b hb => by cases hb; exact ⟨hclv, hlvlv⟩⟩
  | _, .thm _ _ _ _ hE _ _ _ hclA hclp hlvlA hlvlp =>
      typeFacts_extend (typeFacts_of_envWfT hE) ⟨hclA, hlvlA, fun b hb => by cases hb; exact ⟨hclp, hlvlp⟩⟩
  | _, .opaque _ _ _ _ _ hE _ _ _ hclA hclv hlvlA hlvlv =>
      typeFacts_extend (typeFacts_of_envWfT hE) ⟨hclA, hlvlA, fun b hb => by cases hb; exact ⟨hclv, hlvlv⟩⟩
  | _, .group _ _ _ _ _ _ _ hE _ _ _ hmem => typeFacts_groupMembersT hmem (typeFacts_of_envWfT hE)

/-- The conditions on one group, read at its recursor node: each field
family-free or the family applied to the parameter locals and family-free
indices; under `Prop` large elimination, no field revealed in the result
indices. -/
def GroupClass (E E' : ResolvedEnv) (f rr : Nat) (rm : CheckedMember) : Prop :=
  ∀ node : RecNode E E' f rr rm,
    (∀ i, RecFieldsDirect f (policyFamilyLevels node.a.family) node.a.family.parameters.length
      node.a.family.indices.length (node.a.constructorViews i).fields 0) ∧
    (UniformProp node.a.family.resultLevel → node.a.policy = .anySort →
      ∀ i k, k < (node.a.constructorViews i).fields.length →
          posOf (.bvar ((node.a.constructorViews i).fields.length - 1 - k)) (node.a.constructorViews i).resultIndices =
            none)

/-- Each constructor's own admission view splits off `np` parameters, and a
member admitted as a recursor is of recursor class. -/
def WalkClass (np : Nat) {S : ResolvedEnv} : {E E' : ResolvedEnv} → {ms : List (Nat × CheckedMember)} →
    GroupMembersT S E ms E' → Prop
  | _, _, _, .nil _ => True
  | _, _, _, .cons _ _ m _ _ _ _ _ _ _ _ _ hadm _ _ _ _ _ hrest =>
      (match hadm with
        | .constructor _ view _ _ _ _ _ => view.parameters.length = np
        | .recursor _ _ _ _ _ _ _ => m.mclass = .recursorM
        | .family _ _ _ _ _ => True) ∧ WalkClass np hrest

-- `WalkB2` is defined in `RcicF3BoundDefs`.

/-- The class of environments. -/
def ClassG : {E : ResolvedEnv} → EnvWfT E → Prop
  | _, .empty => True
  | _, .axiom _ _ _ _ _ _ _ _ _ => False
  | _, .definition _ _ _ _ _ hE _ _ _ _ _ _ _ => ClassG hE
  | _, .thm _ _ _ _ hE _ _ _ _ _ _ _ => ClassG hE
  | _, .opaque _ _ _ _ _ hE _ _ _ _ _ _ _ => ClassG hE
  | _, .group E f fm ctors rr rm E' hE _ _ _ hmem =>
      ClassG hE ∧ GroupClass E E' f rr rm ∧
        ∀ node : RecNode E E' f rr rm, WalkClass node.a.family.parameters.length hmem

-- `BoundG` is defined in `RcicF3BoundDefs`.

end PSet

end Rcic.F3
