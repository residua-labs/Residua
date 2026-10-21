import rcic.RcicSynSortTransport
import rcic.RcicSynEnrich

/-!
Native transport-origin foundation for W1/W2 (S1C, PR #7166).
Certificates retain actual original witnesses. They construct forward
transports; total coverage of arbitrary public AP queries is not asserted.
In particular no identity below compares an arbitrary bvar regularity proof
with a separately chosen canonical spine. `closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- An actual ambient entry, with its domain witness in its original tail. -/
structure AmbientReceipt (E : ResolvedEnv) (a : Nat) (root : LCtx) where
  index : Nat
  inBounds : index < root.length
  domain : Expr Nat
  sort : Level
  slot : root[index]? = some (.assumption domain) ∨
    ∃ v, root[index]? = some (.letBinding domain v)
  native : HasTyT E a (root.drop (index + 1)) domain (.sort sort)

theorem AmbientReceipt.prefix_lt {E : ResolvedEnv} {a : Nat} {root : LCtx}
    (r : AmbientReceipt E a root) :
    (root.drop (r.index + 1)).length < root.length := by
  have h := r.inBounds
  simp only [List.length_drop]
  omega

/-- Selects the stored child, without first weakening it into the full context. -/
def AmbientReceipt.ofCtx {E : ResolvedEnv} {a : Nat} :
    {root : LCtx} → CtxWfT E a root → (i : Nat) → i < root.length →
      {r : AmbientReceipt E a root // r.index = i}
  | _, .nil, _, hi => by simp at hi
  | _, .assumption _ A u _ hA, 0, hi =>
      ⟨⟨0, hi, A, u, Or.inl (by simp), hA⟩, rfl⟩
  | _, .letBinding _ A u v _ hA _, 0, hi =>
      ⟨⟨0, hi, A, u, Or.inr ⟨v, by simp⟩, hA⟩, rfl⟩
  | _, .assumption _ _ _ C _, i + 1, hi => by
      let r := AmbientReceipt.ofCtx C i (by simpa using hi)
      refine ⟨⟨i + 1, hi, r.val.domain, r.val.sort, ?_, ?_⟩, rfl⟩
      · simpa only [List.getElem?_cons_succ, r.property] using r.val.slot
      · simpa only [List.drop_succ_cons, r.property] using r.val.native
  | _, .letBinding _ _ _ _ C _ _, i + 1, hi => by
      let r := AmbientReceipt.ofCtx C i (by simpa using hi)
      refine ⟨⟨i + 1, hi, r.val.domain, r.val.sort, ?_, ?_⟩, rfl⟩
      · simpa only [List.getElem?_cons_succ, r.property] using r.val.slot
      · simpa only [List.drop_succ_cons, r.property] using r.val.native

/-- A forward chain retains the original ambient receipt, not the new tail's size. -/
structure TransportedAmbient (E : ResolvedEnv) (a : Nat) (root : LCtx)
    (n : Nat) (Γ : LCtx) (A : Expr Nat) (u : Level) where
  original : AmbientReceipt E a root
  chain : SortTyTransport E a (root.drop (original.index + 1))
    original.domain original.sort n Γ A u

/-- The canonical endpoint stores one materialized native object. -/
structure CanonicalSortWitness (E : ResolvedEnv) (n : Nat) (Γ : LCtx)
    (A : Expr Nat) (u : Level) where
  native : HasTyT E n Γ A (.sort u)

def TransportedAmbient.materialize {E : ResolvedEnv} {a n : Nat}
    {root Γ : LCtx} {A : Expr Nat} {u : Level}
    (p : TransportedAmbient E a root n Γ A u) : CanonicalSortWitness E n Γ A u :=
  ⟨p.chain.run p.original.native⟩

theorem TransportedAmbient.materialize_native {E : ResolvedEnv} {a n : Nat}
    {root Γ : LCtx} {A : Expr Nat} {u : Level}
    (p : TransportedAmbient E a root n Γ A u) :
    p.materialize.native = p.chain.run p.original.native := rfl

/-- Receipt descent concerns the original prefix even after transports grow Γ. -/
theorem TransportedAmbient.prefix_lt {E : ResolvedEnv} {a n : Nat}
    {root Γ : LCtx} {A : Expr Nat} {u : Level}
    (p : TransportedAmbient E a root n Γ A u) :
    (root.drop (p.original.index + 1)).length < root.length :=
  p.original.prefix_lt

/-- Extend by a typed chain while keeping the original root and prefix receipt. -/
def TransportedAmbient.extend {E : ResolvedEnv} {a n k : Nat}
    {root Γ Ξ : LCtx} {A B : Expr Nat} {u v : Level}
    (p : TransportedAmbient E a root n Γ A u)
    (q : SortTyTransport E n Γ A u k Ξ B v) :
    TransportedAmbient E a root k Ξ B v :=
  ⟨p.original, p.chain.append q⟩

theorem TransportedAmbient.extend_original {E : ResolvedEnv} {a n k : Nat}
    {root Γ Ξ : LCtx} {A B : Expr Nat} {u v : Level}
    (p : TransportedAmbient E a root n Γ A u)
    (q : SortTyTransport E n Γ A u k Ξ B v) :
    (p.extend q).original = p.original := rfl

theorem TransportedAmbient.extend_materialize {E : ResolvedEnv} {a n k : Nat}
    {root Γ Ξ : LCtx} {A B : Expr Nat} {u v : Level}
    (p : TransportedAmbient E a root n Γ A u)
    (q : SortTyTransport E n Γ A u k Ξ B v) :
    (p.extend q).materialize.native = q.run p.materialize.native :=
  SortTyTransport.run_append p.chain q p.original.native

/-- Append a substitution; its exact sort and original index are unchanged. -/
def TransportedAmbient.esub {E : ResolvedEnv} {a n : Nat}
    {root Γ : LCtx} {A : Expr Nat} {u : Level}
    (p : TransportedAmbient E a root n Γ A u)
    (v t : Expr Nat) (j : Nat) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    TransportedAmbient E a root n (substRemove v j Γ)
      (instantiate j (lift 0 j v) A) u :=
  ⟨p.original, .esub p.chain v t j hcl hinst hget hv⟩

theorem TransportedAmbient.esub_original {E : ResolvedEnv} {a n : Nat}
    {root Γ : LCtx} {A : Expr Nat} {u : Level}
    (p : TransportedAmbient E a root n Γ A u)
    (v t : Expr Nat) (j : Nat) (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)) :
    (p.esub v t j hcl hinst hget hv).original = p.original := rfl

/-- Enrichment preserves the exact recorded expression and sort. AP is separate. -/
noncomputable def CanonicalSortWitness.enrich {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A : Expr Nat} {u : Level}
    (w : CanonicalSortWitness E n Γ A u) (hE : EnvWfT E) (hΓ : CtxWfT E n Γ) :
    TyP E n Γ A (.sort u) := enrichHasTyT_of_envWfT hE hΓ w.native

/-- Retains the actual introducing node and precisely its domain child. -/
inductive BinderDomain {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} (hA : TyP E n Γ A (.sort u)) :
    {e T : Expr Nat} → TyP E n Γ e T → Type
  | pi {B : Expr Nat} {v : Level}
      (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
      BinderDomain hA (.pi E n Γ A u B v hA hB)
  | lam {body B : Expr Nat} {v : Level}
      (hb : TyP E n (.assumption A :: Γ) body B)
      (hB : TyP E n (.assumption A :: Γ) B (.sort v)) :
      BinderDomain hA (.lam E n Γ A u body B v hA hb hB)
  | letE {value B body : Expr Nat} {w : Level}
      (hv : TyP E n Γ value A)
      (hb : TyP E n (.letBinding A value :: Γ) body B)
      (hT : TyP E n Γ (instantiate0 value B) (.sort w)) :
      BinderDomain hA (.letE E n Γ A u value B body w hA hv hb hT)

theorem BinderDomain.wt_lt (Aw : Nat → Nat) {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {A : Expr Nat} {u : Level} {hA : TyP E n Γ A (.sort u)}
    {e T : Expr Nat} {N : TyP E n Γ e T} (r : BinderDomain hA N) :
    hA.wt Aw < N.wt Aw := by
  cases r <;> simp only [TyP.wt] <;> omega

inductive SlotOriginKind where
  | ambient | ambientTransported | binderIntroduced
  deriving DecidableEq

/-- The third origin carries a typed transport, not a sort-alignment oracle. -/
inductive SlotOrigin (E : ResolvedEnv) : Type
  | ambient {a : Nat} {root : LCtx} (r : AmbientReceipt E a root)
  | ambientTransported {a n : Nat} {root Γ : LCtx} {A : Expr Nat} {u : Level}
      (p : TransportedAmbient E a root n Γ A u)
  | binderIntroduced {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
      (hA : TyP E n Γ A (.sort u)) {e T : Expr Nat} (N : TyP E n Γ e T)
      (receipt : BinderDomain hA N)

def SlotOrigin.kind {E : ResolvedEnv} : SlotOrigin E → SlotOriginKind
  | .ambient _ => .ambient
  | .ambientTransported _ => .ambientTransported
  | .binderIntroduced _ _ _ => .binderIntroduced

end Rcic.Syn
