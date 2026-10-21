import rcic.RcicPEqT
import rcic.RcicParRedT
import rcic.RcicParRedSRTyped
import rcic.RcicDT0709EnvWf
import rcic.RcicAnnSemPrefixRows

/-!
# Raw PEqT: proof-front obstructions and a non-transitive triple

This module uses the original `PEqT` inductive, without changing its
constructors or introducing a replacement relation.

First, the universal `hproofR` / `hproofL` signatures of the legacy
conditional consumers in `RcicPEqTSymmTrans` have no inhabitant at
`emptyEnv`. Those signatures accept arbitrary source typing, without
requiring its type to be a proposition. Applying either front to
`sort 0 ≈P sort 0` and `sort 0 : sort 1` would make `sort 0` a proof.

There is also a stronger obstruction: adding only that missing
proposition premise does not repair either universal raw-input front.
The loose proof leaf relates proofs of different propositions, and raw
application congruence can replace a well-typed argument with a proof
that does not have the function's domain type. The resulting raw term
need not have any typing.

The concrete closed terms below are:

* `P = forall X : Prop, X -> X`, with proof `p`;
* `Q = forall T : Type, P`, with proof `other`;
* `q = (fun z : P => z) p` and `r = (fun z : P => z) other`.

The actual relation has `p ≈P q` and `q ≈P r`, but not `p ≈P r`.
The first two terms are proofs of `P`; the final term `r` has no type.
Thus this is a refutation of transitivity of the raw relation, not of
transitivity restricted to an interface with suitable typed endpoints.
The existing conditional consumers remain valid conditional functions;
their universally quantified suppliers are the contracts refuted here.

The negative typing claims use the existing rows at `emptyEnv`, supplied
by the semantic-prefix bridge in its actual scope. No general row or
uniqueness premise is added, and no unrestricted EnvWfT closure theorem
is claimed. All Nonempty eliminations occur within Prop.
`closure_claim = 0`.
-/

namespace Rcic.Declarative

private theorem peqProofFront_emptyRows (n : Nat) : TypedRowsWf emptyEnv n :=
  Ann.typedRowsWf_of_envWfT_semPrefix EnvWfT.empty (by trivial) n

/-- `sort 0` cannot be a proof of any proposition in the empty
environment and empty context. The sort contradiction is `2 = 0`. -/
theorem peqT_sort_zero_not_proof_empty {n : Nat} {P : Expr Nat}
    (hP : HasTyT emptyEnv n [] P (.sort .zero))
    (hs : HasTyT emptyEnv n [] (.sort .zero) P) : False := by
  have hc := TyConvT.symmT (hasTyTInv_sortT hs rfl)
  obtain ⟨c⟩ := convT_of_tyConvT_sort_scope
    EnvWfT.empty (by trivial) CtxWfT.nil hP hc
  obtain ⟨ht⟩ := (DT009T_endpoints_envWfT
    EnvWfT.empty CtxWfT.nil c).2
  have hz := (peqProofFront_emptyRows n).sortRow CtxWfT.nil
    (hasTyTInv_sortT ht rfl)
  have hv : (some 2 : Option Nat) = some 0 := hz (fun _ => none)
  cases hv

/-- The exact legacy right-proof supplier shape is impossible. Its
input permits `Q = sort 1`, so reflexivity already refutes it. -/
theorem no_peqT_legacy_proofR_empty {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {x y Q : Expr Nat},
      PEqT emptyEnv n Δ x y → HasTyT emptyEnv n Δ x Q →
      Σ' P, HasTyT emptyEnv n Δ P (.sort .zero) ×'
        HasTyT emptyEnv n Δ y P) := by
  rintro ⟨hproofR⟩
  obtain ⟨P, hP, hs⟩ := hproofR
    (PEqT.sort [] .zero .zero (fun _ => rfl))
    (HasTyT.sort [] .zero)
  exact peqT_sort_zero_not_proof_empty hP hs

/-- The dual legacy left-proof supplier has the same reflexive
counterexample. This refutes its premise, not its conditional consumer. -/
theorem no_peqT_legacy_proofL_empty {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {x y Q : Expr Nat},
      PEqT emptyEnv n Δ x y → HasTyT emptyEnv n Δ y Q →
      Σ' P, HasTyT emptyEnv n Δ P (.sort .zero) ×'
        HasTyT emptyEnv n Δ x P) := by
  rintro ⟨hproofL⟩
  obtain ⟨P, hP, hs⟩ := hproofL
    (PEqT.sort [] .zero .zero (fun _ => rfl))
    (HasTyT.sort [] .zero)
  exact peqT_sort_zero_not_proof_empty hP hs

namespace PEqTProofFront

/-- The proposition `forall X : Prop, X -> X`. -/
def P : Expr Nat :=
  .pi (.sort .zero) (.pi (.bvar 0) (.bvar 1))

/-- Its identity proof. -/
def p : Expr Nat :=
  .lam (.sort .zero) (.lam (.bvar 0) (.bvar 0))

/-- A different proposition, `forall T : Type, P`. -/
def Q : Expr Nat :=
  .pi (.sort (.succ .zero)) P

/-- A proof of Q whose outer domain cannot be converted to Prop. -/
def other : Expr Nat :=
  .lam (.sort (.succ .zero)) p

/-- Identity with the fixed domain P. -/
def idP : Expr Nat := .lam P (.bvar 0)

/-- A well-typed application, also a proof of P. -/
def q : Expr Nat := .app idP p

/-- The same function with the heterogeneous proof used as argument. -/
def r : Expr Nat := .app idP other

/-- P is a proposition. Its bound variables make these typings work
in any surrounding context; no environment lookup is used. -/
def P_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ P (.sort .zero) :=
  .conv Γ P
    (.sort (.imax (.succ .zero) (.imax .zero .zero)))
    (.sort .zero)
    (.succ (.imax (.succ .zero) (.imax .zero .zero)))
    (.pi Γ (.sort .zero) (.succ .zero)
      (.pi (.bvar 0) (.bvar 1)) (.imax .zero .zero)
      (.sort Γ .zero)
      (.pi (.assumption (.sort .zero) :: Γ)
        (.bvar 0) .zero (.bvar 1) .zero
        (.bvar _ 0 (.sort .zero) rfl)
        (.bvar _ 1 (.sort .zero) rfl)))
    (.sorts Γ (.imax (.succ .zero) (.imax .zero .zero))
      .zero (fun _ => rfl))

/-- The literal lambda proof of P. -/
def p_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ p P :=
  .lam Γ (.sort .zero) (.succ .zero)
    (.lam (.bvar 0) (.bvar 0)) (.pi (.bvar 0) (.bvar 1))
    (.sort Γ .zero)
    (.lam (.assumption (.sort .zero) :: Γ)
      (.bvar 0) .zero (.bvar 0) (.bvar 1)
      (.bvar _ 0 (.sort .zero) rfl)
      (.bvar _ 0 (.bvar 1) rfl))

/-- Impredicativity makes Q a proposition as well. -/
def Q_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ Q (.sort .zero) :=
  .conv Γ Q
    (.sort (.imax (.succ (.succ .zero)) .zero))
    (.sort .zero) (.succ (.imax (.succ (.succ .zero)) .zero))
    (.pi Γ (.sort (.succ .zero)) (.succ (.succ .zero)) P .zero
      (.sort Γ (.succ .zero))
      (P_ty (.assumption (.sort (.succ .zero)) :: Γ)))
    (.sorts Γ (.imax (.succ (.succ .zero)) .zero)
      .zero (fun _ => rfl))

/-- The heterogeneous argument has an actual typing, at Q. -/
def other_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ other Q :=
  .lam Γ (.sort (.succ .zero)) (.succ (.succ .zero)) p P
    (.sort Γ (.succ .zero))
    (p_ty (.assumption (.sort (.succ .zero)) :: Γ))

/-- Identity on P. P is closed, so its lift under this binder is P. -/
def idP_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ idP (.pi P P) :=
  .lam Γ P .zero (.bvar 0) P (P_ty Γ)
    (.bvar (.assumption P :: Γ) 0 P rfl)

/-- The middle term really is a proof of P. -/
def q_ty {E : ResolvedEnv} {n : Nat} (Γ : LCtx) :
    HasTyT E n Γ q P :=
  .app Γ idP p P P (idP_ty Γ) (p_ty Γ)

/-- First edge: the loose proof leaf, here with the common proposition P. -/
def pq {n : Nat} : PEqT emptyEnv n [] p q :=
  .proof [] p q P P (P_ty []) (P_ty []) (p_ty []) (q_ty [])

/-- Second edge: raw app congruence accepts a heterogeneous proof leaf
in the argument position, with no typing premise for the whole target. -/
def qr {n : Nat} : PEqT emptyEnv n [] q r :=
  .app [] idP idP p other (PEqT.refl idP)
    (.proof [] p other P Q (P_ty []) (Q_ty []) (p_ty []) (other_ty []))

/-- The reverse structural edge is built directly, without assuming
that the full raw PEqT relation is symmetric. -/
def rq {n : Nat} : PEqT emptyEnv n [] r q :=
  .app [] idP idP other p (PEqT.refl idP)
    (.proof [] other p Q P (Q_ty []) (P_ty []) (other_ty []) (p_ty []))

/-- Although other is a proof of Q, it cannot be given type P:
lambda inversion and the actual empty-environment rows would equate
its outer domain `sort 1` with P's outer domain `sort 0`. -/
theorem other_not_P {n : Nat}
    (h : HasTyT emptyEnv n [] other P) : False := by
  obtain ⟨_u, B, _hA, _hb, hidx⟩ := hasTyTInv_lam h rfl
  obtain ⟨hd⟩ := ((peqProofFront_emptyRows n).piRow CtxWfT.nil hidx).1
  have hz := (peqProofFront_emptyRows n).sortRow CtxWfT.nil hd
  have hv : (some 1 : Option Nat) = some 0 := hz (fun _ => none)
  cases hv

/-- The final application has no type at all. Any application typing
would assign idP a Pi type; lambda inversion and the Pi row identify
that type's domain up to TyConvT with P, forcing other : P. -/
theorem r_not_typed {n : Nat} {T : Expr Nat}
    (h : HasTyT emptyEnv n [] r T) : False := by
  obtain ⟨A, B, hf, ha, _hc⟩ := hasTyTInv_app h rfl
  obtain ⟨_u, C, _hP, _hb, hidx⟩ := hasTyTInv_lam hf rfl
  obtain ⟨hd⟩ := ((peqProofFront_emptyRows n).piRow CtxWfT.nil hidx).1
  exact other_not_P (hasTyT_of_tyConvT ha (TyConvT.symmT hd))

private def lam_app_right_proof {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body f a : Expr Nat}
    (h : PEqT E n Γ (.lam A body) (.app f a)) :
    Σ' R, HasTyT E n Γ R (.sort .zero) ×'
      HasTyT E n Γ (.app f a) R :=
  match h with
  | .proof _ _ _ _ R _ hR _ hr => ⟨R, hR, hr⟩

/-- A lambda and an application can be PEqT-related only through the
proof leaf. That leaf would supply the impossible typing of r. -/
theorem not_pr {n : Nat} : ¬ Nonempty (PEqT emptyEnv n [] p r) := by
  rintro ⟨h⟩
  obtain ⟨_R, _hR, hr⟩ := lam_app_right_proof h
  exact r_not_typed hr

/-- A closed, concrete non-transitive triple for the actual raw PEqT.
Both positive edges are supplied as data, not assumed. -/
theorem raw_nontransitive {n : Nat} :
    Nonempty (PEqT emptyEnv n [] p q) ∧
    Nonempty (PEqT emptyEnv n [] q r) ∧
    ¬ Nonempty (PEqT emptyEnv n [] p r) :=
  ⟨⟨pq⟩, ⟨qr⟩, not_pr⟩

end PEqTProofFront

/-- No raw transitivity function exists, already at emptyEnv and the
empty context. This does not quantify over a typed-endpoint restriction. -/
theorem no_peqT_raw_trans_empty {n : Nat} :
    ¬ Nonempty (∀ {a b c : Expr Nat},
      PEqT emptyEnv n [] a b → PEqT emptyEnv n [] b c →
      PEqT emptyEnv n [] a c) := by
  rintro ⟨htrans⟩
  exact PEqTProofFront.not_pr
    ⟨htrans PEqTProofFront.pq PEqTProofFront.qr⟩

/-- Even adding source-proposition typing leaves the universal right
front impossible: qr starts at a real proof but ends at an untypable term. -/
theorem no_peqT_guarded_proofR_empty {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {x y Q : Expr Nat},
      PEqT emptyEnv n Δ x y →
      HasTyT emptyEnv n Δ Q (.sort .zero) →
      HasTyT emptyEnv n Δ x Q →
      Σ' P, HasTyT emptyEnv n Δ P (.sort .zero) ×'
        HasTyT emptyEnv n Δ y P) := by
  rintro ⟨hproofR⟩
  obtain ⟨_P, _hP, hr⟩ := hproofR PEqTProofFront.qr
    (PEqTProofFront.P_ty []) (PEqTProofFront.q_ty [])
  exact PEqTProofFront.r_not_typed hr

/-- The left front remains impossible with the same added guard,
using the directly constructed reverse structural edge rq. -/
theorem no_peqT_guarded_proofL_empty {n : Nat} :
    ¬ Nonempty (∀ {Δ : LCtx} {x y Q : Expr Nat},
      PEqT emptyEnv n Δ x y →
      HasTyT emptyEnv n Δ Q (.sort .zero) →
      HasTyT emptyEnv n Δ y Q →
      Σ' P, HasTyT emptyEnv n Δ P (.sort .zero) ×'
        HasTyT emptyEnv n Δ x P) := by
  rintro ⟨hproofL⟩
  obtain ⟨_P, _hP, hr⟩ := hproofL PEqTProofFront.rq
    (PEqTProofFront.P_ty []) (PEqTProofFront.q_ty [])
  exact PEqTProofFront.r_not_typed hr

#print axioms peqT_sort_zero_not_proof_empty
#print axioms no_peqT_legacy_proofR_empty
#print axioms no_peqT_legacy_proofL_empty
#print axioms PEqTProofFront.P_ty
#print axioms PEqTProofFront.p_ty
#print axioms PEqTProofFront.Q_ty
#print axioms PEqTProofFront.other_ty
#print axioms PEqTProofFront.idP_ty
#print axioms PEqTProofFront.q_ty
#print axioms PEqTProofFront.pq
#print axioms PEqTProofFront.qr
#print axioms PEqTProofFront.rq
#print axioms PEqTProofFront.other_not_P
#print axioms PEqTProofFront.r_not_typed
#print axioms PEqTProofFront.not_pr
#print axioms PEqTProofFront.raw_nontransitive
#print axioms no_peqT_raw_trans_empty
#print axioms no_peqT_guarded_proofR_empty
#print axioms no_peqT_guarded_proofL_empty

end Rcic.Declarative
