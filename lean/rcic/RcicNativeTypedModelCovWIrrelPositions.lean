import rcic.RcicNativeTypedModelCovWEtaAligned

/-!
# Native proof positions at a declared universe instance

The prefix domains remain open under their preceding telescope binders.
They are placed newest first in the native context.  The universe vector
is an index of the predicate; it is not selected from an erased compact.
Native typing is Type-valued, so its existence is recorded by `Nonempty`.
No decision procedure for native typing or conversion is assumed.

`CovWIrrelSlot` is a constructive graph of the requested field operation.
An already-bottom field needs no proof-position decision.  A nonbottom
field is erased with positive native proof-position evidence and retained
with evidence that the position is not a proof position.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit

open Rcic.Declarative Rcic.Declarative.NativeValleys
open FamModelLRSAudit PiModelDeltaIotaAudit TypedModelAudit
open TypedModelCovWAudit TypedModelCovWEtaAudit

/-- Telescope domains are stored outermost first; native contexts are newest first. -/
def covWIrrelTelCtx (ds : List (Expr Nat)) : LCtx :=
  ds.reverse.map LocalDecl.assumption

/-- An actual declared binder, after substituting the supplied universe vector.
Earlier term arguments are represented by the telescope context, not substituted
into the domain. -/
def CovWIrrelPosition (E : ResolvedEnv) (n r : Nat) (ls : List Level)
    (i : Nat) (ds : List (Expr Nat)) (D B : Expr Nat) : Prop :=
  ∃ m, E.members r = some m ∧ ls.length = m.arity ∧
    levelsBounded n ls = true ∧
    peelPis i (instantiateLevels ls m.mtype) = some (ds, .pi D B)

/-- A declared binder is a proof position exactly when its native domain is
typed at `Sort 0` in the preceding telescope context, at these universe levels. -/
def CovWIrrelProofPosition (E : ResolvedEnv) (n r : Nat)
    (ls : List Level) (i : Nat) : Prop :=
  ∃ ds D B, CovWIrrelPosition E n r ls i ds D B ∧
    Nonempty (HasTyT E n (covWIrrelTelCtx ds) D (.sort .zero))

theorem covWIrrel_position_length {E : ResolvedEnv} {n r i : Nat}
    {ls : List Level} {ds : List (Expr Nat)} {D B : Expr Nat}
    (h : CovWIrrelPosition E n r ls i ds D B) : ds.length = i := by
  obtain ⟨m, _, _, _, hp⟩ := h
  exact peelPis_length i (instantiateLevels ls m.mtype) hp

/-- The declaration lookup and syntactic peel fix all the telescope data. -/
theorem covWIrrel_position_unique {E : ResolvedEnv} {n r i : Nat}
    {ls : List Level} {ds ds' : List (Expr Nat)} {D B D' B' : Expr Nat}
    (h : CovWIrrelPosition E n r ls i ds D B)
    (h' : CovWIrrelPosition E n r ls i ds' D' B') :
    ds = ds' ∧ D = D' ∧ B = B' := by
  obtain ⟨m, hm, _, _, hp⟩ := h
  obtain ⟨m', hm', _, _, hp'⟩ := h'
  have hmem : m = m' := Option.some.inj (hm.symm.trans hm')
  subst m'
  have hpair : (ds, Expr.pi D B) = (ds', Expr.pi D' B') :=
    Option.some.inj (hp.symm.trans hp')
  cases hpair
  exact ⟨rfl, rfl, rfl⟩

/-- With the actual position supplied, the existential definition has exactly
the native proof-typing content of that position. -/
theorem covWIrrel_proofPosition_iff {E : ResolvedEnv} {n r i : Nat}
    {ls : List Level} {ds : List (Expr Nat)} {D B : Expr Nat}
    (h : CovWIrrelPosition E n r ls i ds D B) :
    CovWIrrelProofPosition E n r ls i ↔
      Nonempty (HasTyT E n (covWIrrelTelCtx ds) D (.sort .zero)) := by
  constructor
  · rintro ⟨ds', D', B', h', ht⟩
    obtain ⟨rfl, rfl, rfl⟩ := covWIrrel_position_unique h h'
    exact ht
  · intro ht
    exact ⟨ds, D, B, h, ht⟩

/-- The two native cases plus the computationally unconditional bottom case.
The predicate `P` is external to the observation relation being defined. -/
inductive CovWIrrelSlot (P : Prop) : CptT → CptT → Prop
  | bot : CovWIrrelSlot P .bot .bot
  | proof (h : P) (u : CptT) : CovWIrrelSlot P u .bot
  | keep (h : ¬ P) (u : CptT) : CovWIrrelSlot P u u

theorem covWIrrel_slot_proof {P : Prop} {u v : CptT}
    (h : CovWIrrelSlot P u v) (hp : P) : v = .bot := by
  cases h with
  | bot => rfl
  | proof => rfl
  | keep hn => exact (hn hp).elim

theorem covWIrrel_slot_nonproof {P : Prop} {u v : CptT}
    (h : CovWIrrelSlot P u v) (hn : ¬ P) : v = u := by
  cases h with
  | bot => rfl
  | proof hp => exact (hn hp).elim
  | keep => rfl

/-- Preserving an argument already equal to bottom is distinct from erasing
a nonbottom argument.  The latter has the exact native proof-position iff. -/
theorem covWIrrel_slot_bot_iff {P : Prop} {u v : CptT}
    (h : CovWIrrelSlot P u v) (hu : u ≠ .bot) : v = .bot ↔ P := by
  constructor
  · intro hv
    cases h with
    | bot => exact (hu rfl).elim
    | proof hp => exact hp
    | keep => exact (hu hv).elim
  · exact covWIrrel_slot_proof h

theorem covWIrrel_slot_deterministic {P : Prop} {u v w : CptT}
    (h : CovWIrrelSlot P u v) (h' : CovWIrrelSlot P u w) : v = w := by
  cases h with
  | bot =>
      cases h' <;> rfl
  | proof hp => exact (covWIrrel_slot_proof h' hp).symm
  | keep hn => exact (covWIrrel_slot_nonproof h' hn).symm

/-- Existence for a nonbottom input exposes precisely the local excluded-middle
certificate.  The relation itself does not assume such a certificate globally. -/
theorem covWIrrel_slot_exists_iff {P : Prop} {u : CptT} (hu : u ≠ .bot) :
    (∃ v, CovWIrrelSlot P u v) ↔ P ∨ ¬ P := by
  constructor
  · rintro ⟨v, h⟩
    cases h with
    | bot => exact (hu rfl).elim
    | proof hp => exact Or.inl hp
    | keep hn => exact Or.inr hn
  · intro h
    rcases h with hp | hn
    · exact ⟨.bot, .proof hp u⟩
    · exact ⟨u, .keep hn u⟩

/-- The old raw valuation interface can supply a spine without any declaration
at its compact head.  A new declaration/level certificate therefore cannot be
recovered from the old `appSpine` function premise in full generality. -/
theorem covWIrrel_raw_origin_boundary (r : Nat) :
    ApproxTW emptyEnv (fun _ c => c = .spine r [])
      (.bvar 0) (.spine r []) ∧
    ¬ ∃ m, emptyEnv.members r = some m := by
  refine ⟨.bvar rfl, ?_⟩
  rintro ⟨m, hm⟩
  cases hm

/-- Even at a rigid constant, the old compact erases the supplied universe
vector.  This theorem is about that representation, not a claim that a
particular pair of universe arguments passes native arity checking. -/
theorem covWIrrel_raw_levels_boundary {E : ResolvedEnv} {r : Nat}
    (hr : RigidConst E r) (hnp : ¬ PropCtorT E r)
    (ρ : EnvT) (ls ls' : List Level) (hne : ls ≠ ls') :
    ¬ ∃ decode : CptT → List Level,
      (∀ c, ApproxTW E ρ (.const r ls) c → c ≠ .bot → decode c = ls) ∧
      (∀ c, ApproxTW E ρ (.const r ls') c → c ≠ .bot → decode c = ls') := by
  rintro ⟨decode, hleft, hright⟩
  have hl := hleft (.spine r []) (.const ρ r ls hr hnp) CptT.noConfusion
  have hr' := hright (.spine r []) (.const ρ r ls' hr hnp) CptT.noConfusion
  exact hne (hl.symm.trans hr')

-- BEGIN RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_POSITIONS_ROOTS
#print axioms covWIrrelTelCtx
#print axioms CovWIrrelPosition
#print axioms CovWIrrelProofPosition
#print axioms covWIrrel_position_length
#print axioms covWIrrel_position_unique
#print axioms covWIrrel_proofPosition_iff
#print axioms CovWIrrelSlot
#print axioms covWIrrel_slot_proof
#print axioms covWIrrel_slot_nonproof
#print axioms covWIrrel_slot_bot_iff
#print axioms covWIrrel_slot_deterministic
#print axioms covWIrrel_slot_exists_iff
#print axioms covWIrrel_raw_origin_boundary
#print axioms covWIrrel_raw_levels_boundary
-- END RCIC_NATIVE_TYPED_MODEL_COV_W_IRREL_POSITIONS_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelCovWIrrelAudit
