import rcic.RcicNativeTypedModelKTransport

/-!
# A transitive fragment on which the old model can be reused

An allowed set of constant references excludes indexed proposition recursors,
and is closed under every delta body and structured recursor schema that the
old approximation rules may inspect.  A fragment expression names only members
of such a set.  The set is a predicate, so recursive Nat schemas do not require
an infinite syntax proof.  Literal references are those of the already landed
`occursConst`; there is no second reference collector here.

`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelDeltaIotaAudit
open Rcic.Declarative.NativeValleys.TypedModelAudit
open Rcic.Declarative.NativeValleys.TypedModelKTransportAudit

variable {E : ResolvedEnv}

/-- Closure concerns exactly the hidden expressions inspected by `ApproxT`. -/
structure KFreeSetT (E : ResolvedEnv) (S : Nat → Prop) : Prop where
  noIndexed : ∀ r, S r → ¬ IndexedPropRecT E r
  delta : ∀ {r m b}, S r → DeltaConst E r m b →
    ∀ ls k, occursConst k (instantiateLevels ls b) = true → S k
  schema : ∀ (w : IotaWitnessS E), S w.recRef →
    ∀ ls k, occursConst k (instantiateLevels ls w.schema) = true → S k

/-- The K-free fragment includes closure through transparent bodies and schemas. -/
def KFreeT (E : ResolvedEnv) (e : Expr Nat) : Prop :=
  ∃ S : Nat → Prop, KFreeSetT E S ∧ ∀ r, occursConst r e = true → S r

theorem kFreeSetT_empty (E : ResolvedEnv) : KFreeSetT E (fun _ => False) :=
  ⟨fun _ h => h.elim, fun h => h.elim, fun _ h => h.elim⟩

theorem kFreeSetT_union {S T : Nat → Prop}
    (hS : KFreeSetT E S) (hT : KFreeSetT E T) :
    KFreeSetT E (fun r => S r ∨ T r) where
  noIndexed := fun r h => h.elim (hS.noIndexed r) (hT.noIndexed r)
  delta := fun h hd ls k hk =>
    h.elim (fun hs => Or.inl (hS.delta hs hd ls k hk))
      (fun ht => Or.inr (hT.delta ht hd ls k hk))
  schema := fun w h ls k hk =>
    h.elim (fun hs => Or.inl (hS.schema w hs ls k hk))
      (fun ht => Or.inr (hT.schema w ht ls k hk))

theorem kFreeT_of_no_occurs {e : Expr Nat}
    (h : ∀ r, occursConst r e = false) : KFreeT E e := by
  refine ⟨fun _ => False, kFreeSetT_empty E, ?_⟩
  intro r hr
  rw [h r] at hr
  cases hr

theorem kFreeT_bvar (E : ResolvedEnv) (i : Nat) : KFreeT E (.bvar i) :=
  kFreeT_of_no_occurs (fun _ => rfl)

theorem kFreeT_sort (E : ResolvedEnv) (l : Level) : KFreeT E (.sort l) :=
  kFreeT_of_no_occurs (fun _ => rfl)

/-- One expression's constant support being contained in another's suffices. -/
theorem kFreeT_support {e f : Expr Nat} (hf : KFreeT E f)
    (hsub : ∀ r, occursConst r e = true → occursConst r f = true) : KFreeT E e := by
  obtain ⟨S, hS, hmem⟩ := hf
  exact ⟨S, hS, fun r hr => hmem r (hsub r hr)⟩

private theorem kFreeT_binary {a b e : Expr Nat}
    (h : ∀ r, occursConst r e = (occursConst r a || occursConst r b))
    (ha : KFreeT E a) (hb : KFreeT E b) : KFreeT E e := by
  obtain ⟨S, hS, hs⟩ := ha
  obtain ⟨T, hT, ht⟩ := hb
  refine ⟨fun r => S r ∨ T r, kFreeSetT_union hS hT, ?_⟩
  intro r hr
  rw [h r, Bool.or_eq_true] at hr
  exact hr.elim (fun h => Or.inl (hs r h)) (fun h => Or.inr (ht r h))

theorem kFreeT_app {a b : Expr Nat} (ha : KFreeT E a) (hb : KFreeT E b) :
    KFreeT E (.app a b) := kFreeT_binary (fun _ => rfl) ha hb

theorem kFreeT_pi {a b : Expr Nat} (ha : KFreeT E a) (hb : KFreeT E b) :
    KFreeT E (.pi a b) := kFreeT_binary (fun _ => rfl) ha hb

theorem kFreeT_lam {a b : Expr Nat} (ha : KFreeT E a) (hb : KFreeT E b) :
    KFreeT E (.lam a b) := kFreeT_binary (fun _ => rfl) ha hb

theorem kFreeT_app_iff (a b : Expr Nat) :
    KFreeT E (.app a b) ↔ KFreeT E a ∧ KFreeT E b := by
  constructor
  · intro h
    exact ⟨kFreeT_support h (fun r hr => by simp [occursConst, hr]),
      kFreeT_support h (fun r hr => by simp [occursConst, hr])⟩
  · exact fun ⟨ha, hb⟩ => kFreeT_app ha hb

theorem kFreeT_pi_iff (a b : Expr Nat) :
    KFreeT E (.pi a b) ↔ KFreeT E a ∧ KFreeT E b := by
  constructor
  · intro h
    exact ⟨kFreeT_support h (fun r hr => by simp [occursConst, hr]),
      kFreeT_support h (fun r hr => by simp [occursConst, hr])⟩
  · exact fun ⟨ha, hb⟩ => kFreeT_pi ha hb

theorem kFreeT_lam_iff (a b : Expr Nat) :
    KFreeT E (.lam a b) ↔ KFreeT E a ∧ KFreeT E b := by
  constructor
  · intro h
    exact ⟨kFreeT_support h (fun r hr => by simp [occursConst, hr]),
      kFreeT_support h (fun r hr => by simp [occursConst, hr])⟩
  · exact fun ⟨ha, hb⟩ => kFreeT_lam ha hb

theorem kFreeT_letE_iff (A v b : Expr Nat) :
    KFreeT E (.letE A v b) ↔ KFreeT E (.app (.lam A b) v) := by
  constructor <;> intro h <;> apply kFreeT_support h <;> intro r hr
  · simpa only [occursConst, Bool.or_eq_true, or_assoc, or_left_comm, or_comm] using hr
  · simpa only [occursConst, Bool.or_eq_true, or_assoc, or_left_comm, or_comm] using hr

theorem kFreeT_const_not_indexed {r : Nat} {ls : List Level}
    (h : KFreeT E (.const r ls)) : ¬ IndexedPropRecT E r := by
  obtain ⟨S, hS, hm⟩ := h
  exact hS.noIndexed r (hm r (by simp [occursConst]))

theorem kFreeT_delta {r : Nat} {ls ls' : List Level} {m : CheckedMember} {b : Expr Nat}
    (h : KFreeT E (.const r ls)) (hd : DeltaConst E r m b) :
    KFreeT E (instantiateLevels ls' b) := by
  obtain ⟨S, hS, hm⟩ := h
  exact ⟨S, hS, hS.delta (hm r (by simp [occursConst])) hd ls'⟩

theorem kFreeT_schema (w : IotaWitnessS E) {ls ls' : List Level}
    (h : KFreeT E (.const w.recRef ls)) :
    KFreeT E (instantiateLevels ls' w.schema) := by
  obtain ⟨S, hS, hm⟩ := h
  exact ⟨S, hS, hS.schema w (hm _ (by simp [occursConst])) ls'⟩

theorem kFreeT_foldApps_head {f : Expr Nat} {xs : List (Expr Nat)}
    (h : KFreeT E (foldApps f xs)) : KFreeT E f := by
  induction xs generalizing f with
  | nil => exact h
  | cons x xs ih => exact ((kFreeT_app_iff _ _).mp (ih h)).1

/-- Rigid members have neither an inspected delta body nor a recursor schema. -/
theorem kFreeT_rigid_const {r : Nat} (hr : RigidConst E r) (ls : List Level) :
    KFreeT E (.const r ls) := by
  refine ⟨fun k => k = r, ?_, ?_⟩
  · constructor
    · intro k hk
      subst k
      rintro ⟨w, hw, _, _⟩
      exact (hr w.recMember (hw ▸ w.hrec)).2 w.hrecK
    · intro k m b hk hd
      subst k
      exact (not_rigidConst_of_deltaConst hd hr).elim
    · intro w hw
      exact ((hr w.recMember (hw ▸ w.hrec)).2 w.hrecK).elim
  · intro k hk
    have hrk : r = k := of_decide_eq_true hk
    exact hrk.symm

/-- No restricted set is needed when the environment has no affected recursor. -/
theorem kFreeT_of_no_indexed (hE : ∀ r, ¬ IndexedPropRecT E r) (e : Expr Nat) :
    KFreeT E e :=
  ⟨fun _ => True, ⟨fun r _ => hE r, fun _ _ _ _ _ => trivial,
    fun _ _ _ _ _ => trivial⟩, fun _ _ => trivial⟩

/-- This includes all recursive Nat schemas and the Nat recursor itself. -/
theorem kFreeT_natEnvU (e : Expr Nat) : KFreeT natEnvU e :=
  kFreeT_of_no_indexed not_indexedPropRecT_natEnvU e

theorem not_kFreeT_eqRec (ls : List Level) : ¬ KFreeT eqEnvT (.const 65 ls) :=
  fun h => kFreeT_const_not_indexed h indexedPropRecT_eqRec

theorem not_kFreeT_eqRec_spine (ls : List Level) (xs : List (Expr Nat)) :
    ¬ KFreeT eqEnvT (foldApps (.const 65 ls) xs) :=
  fun h => not_kFreeT_eqRec ls (kFreeT_foldApps_head h)

-- BEGIN RCIC_NATIVE_TYPED_MODEL_K_FRAGMENT_ROOTS
#print axioms KFreeSetT
#print axioms KFreeSetT.mk
#print axioms KFreeSetT.noIndexed
#print axioms KFreeSetT.delta
#print axioms KFreeSetT.schema
#print axioms KFreeT
#print axioms kFreeSetT_empty
#print axioms kFreeSetT_union
#print axioms kFreeT_of_no_occurs
#print axioms kFreeT_bvar
#print axioms kFreeT_sort
#print axioms kFreeT_support
#print axioms kFreeT_app
#print axioms kFreeT_pi
#print axioms kFreeT_lam
#print axioms kFreeT_app_iff
#print axioms kFreeT_pi_iff
#print axioms kFreeT_lam_iff
#print axioms kFreeT_letE_iff
#print axioms kFreeT_const_not_indexed
#print axioms kFreeT_delta
#print axioms kFreeT_schema
#print axioms kFreeT_foldApps_head
#print axioms kFreeT_rigid_const
#print axioms kFreeT_of_no_indexed
#print axioms kFreeT_natEnvU
#print axioms not_kFreeT_eqRec
#print axioms not_kFreeT_eqRec_spine
-- END RCIC_NATIVE_TYPED_MODEL_K_FRAGMENT_ROOTS

end Rcic.Declarative.NativeValleys.TypedModelKFragmentAudit
