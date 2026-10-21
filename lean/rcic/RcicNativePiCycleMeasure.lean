import rcic.RcicTypedGroupPins
import rcic.RcicTypedConv
import rcic.RcicTypedInvert
import rcic.RcicTypedStrengthen
import rcic.RcicDT0709EnvWf

/-!
# Π alignment: raw endpoint size and earlier-declaration support do not decrease

Composition-only fixture at the landed admitted `andEnvU`. The family at reference
`0` has the closed declared type `Prop → Prop → Prop`. In the admitted context
`P : Prop`, its very same application `And P P` can be derived with the first node
domain `(fun q : Prop => Prop) (And P P)`, further padded by any number of typed
identity β redexes. The node-to-declaration Π conversion is larger than the fixed
outer Π type and mentions the current family, although its declaration mentions
no constants. All application/conversion derivations below are actual `HasTyT` /
`ConvT` constructors, and application inversion returns the displayed node domain.

This refutes two proposed *syntactic decrease obligations*. It does not refute
Π-injectivity, normalization of this particular β-only witness, nor every possible
well-founded proof order. A successful induction must establish a different
decrease/normalization invariant on alignment requests; declaration closedness
alone does not supply it. `closure_claim = 0`.
-/

namespace Rcic.Declarative.NativePiCycleMeasure

abbrev ctx : LCtx := [.assumption (.sort .zero)]

def ctxWf : CtxWfT andEnvU 0 ctx :=
  .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)

def propVarTy : HasTyT andEnvU 0 ctx (.bvar 0) (.sort .zero) :=
  .bvar ctx 0 (.sort .zero) rfl

abbrev familyApp : Expr Nat := andApp (.bvar 0) (.bvar 0)

def familyAppTy : HasTyT andEnvU 0 ctx familyApp (.sort .zero) :=
  andOfTyT rfl propVarTy propVarTy

/-- A domain convertible to `Prop`, containing the very family being applied. -/
def seedDomain : Expr Nat :=
  .app (.lam (.sort .zero) (.sort .zero)) familyApp

def seedDomainTy : HasTyT andEnvU 0 ctx seedDomain (.sort (.succ .zero)) :=
  .app ctx _ familyApp (.sort .zero) (.sort (.succ .zero))
    (.lam ctx (.sort .zero) (.succ .zero) (.sort .zero) (.sort (.succ .zero))
      (.sort ctx .zero) (.sort _ .zero)) familyAppTy

def seedDomainConv : ConvT andEnvU 0 ctx seedDomain (.sort .zero)
    (.sort (.succ .zero)) :=
  .beta ctx (.sort .zero) (.sort .zero) familyApp (.sort (.succ .zero))
    (.succ .zero) (.sort ctx .zero) (.sort _ .zero) familyAppTy

/-- Arbitrary typed identity β padding, preserving the same head occurrence. -/
def nodeDomain : Nat → Expr Nat
  | 0 => seedDomain
  | k + 1 => .app (.lam (.sort (.succ .zero)) (.bvar 0)) (nodeDomain k)

def nodeDomainTy : (k : Nat) →
    HasTyT andEnvU 0 ctx (nodeDomain k) (.sort (.succ .zero))
  | 0 => seedDomainTy
  | k + 1 =>
      .app ctx _ (nodeDomain k) (.sort (.succ .zero)) (.sort (.succ .zero))
        (.lam ctx (.sort (.succ .zero)) (.succ (.succ .zero)) (.bvar 0)
          (.sort (.succ .zero)) (.sort ctx (.succ .zero)) (.bvar _ 0 _ rfl))
        (nodeDomainTy k)

def nodeDomainConv : (k : Nat) →
    ConvT andEnvU 0 ctx (nodeDomain k) (.sort .zero) (.sort (.succ .zero))
  | 0 => seedDomainConv
  | k + 1 =>
      .trans ctx (nodeDomain (k + 1)) (nodeDomain k) (.sort .zero)
        (.sort (.succ .zero))
        (.beta ctx (.sort (.succ .zero)) (.bvar 0) (nodeDomain k)
          (.sort (.succ .zero)) (.succ (.succ .zero))
          (.sort ctx (.succ .zero)) (.bvar _ 0 _ rfl) (nodeDomainTy k))
        (nodeDomainConv k)

abbrev tailType : Expr Nat := .pi (.sort .zero) (.sort .zero)

def nodePi (k : Nat) : Expr Nat := .pi (nodeDomain k) tailType

/-- The Π comparison obtained when the application's derived node must be
aligned with the family's declared telescope. -/
def declaredToNode (k : Nat) :
    ConvT andEnvU 0 ctx andFamMember.mtype (nodePi k) (.sort andFamSortU) :=
  .pi ctx (.sort .zero) (nodeDomain k) tailType tailType
    (.succ .zero) (.imax (.succ .zero) (.succ .zero))
    (.symm ctx (nodeDomain k) (.sort .zero) (.sort (.succ .zero)) (nodeDomainConv k))
    (.refl _ tailType (.sort (.imax (.succ .zero) (.succ .zero)))
      (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero)))

def nodeToDeclared (k : Nat) :
    TyConvT andEnvU 0 ctx (nodePi k) andFamMember.mtype :=
  .of ctx (nodePi k) andFamMember.mtype andFamSortU
    (.symm ctx andFamMember.mtype (nodePi k) (.sort andFamSortU) (declaredToNode k))

def familyHeadNodeTy (k : Nat) :
    HasTyT andEnvU 0 ctx (.const 0 []) (nodePi k) :=
  .conv ctx (.const 0 []) andFamMember.mtype (nodePi k) andFamSortU
    (.const ctx 0 [] andFamMember rfl rfl rfl) (declaredToNode k)

def argumentNodeTy (k : Nat) : HasTyT andEnvU 0 ctx (.bvar 0) (nodeDomain k) :=
  .conv ctx (.bvar 0) (.sort .zero) (nodeDomain k) (.succ .zero) propVarTy
    (.symm ctx (nodeDomain k) (.sort .zero) (.sort (.succ .zero)) (nodeDomainConv k))

/-- The first real application is typed at its arbitrarily large node domain. -/
def firstAppTy (k : Nat) :
    HasTyT andEnvU 0 ctx (.app (.const 0 []) (.bvar 0)) tailType :=
  .app ctx (.const 0 []) (.bvar 0) (nodeDomain k) tailType
    (familyHeadNodeTy k) (argumentNodeTy k)

/-- No erasure or replacement of the landed application inversion. -/
theorem firstApp_inv_domain (k : Nat) :
    (hasTyTInv_app (firstAppTy k) rfl).1 = nodeDomain k := rfl

def familyAppNodeTy (k : Nat) : HasTyT andEnvU 0 ctx familyApp (.sort .zero) :=
  .app ctx (.app (.const 0 []) (.bvar 0)) (.bvar 0) (.sort .zero) (.sort .zero)
    (firstAppTy k) propVarTy

/-- An actual family-spine `ConvT.app` derivation using that same node domain. -/
def familyAppNodeConv (k : Nat) :
    ConvT andEnvU 0 ctx familyApp familyApp (.sort .zero) :=
  .app ctx (.app (.const 0 []) (.bvar 0)) (.app (.const 0 []) (.bvar 0))
    (.bvar 0) (.bvar 0) (.sort .zero) (.sort .zero)
    (.app ctx (.const 0 []) (.const 0 []) (.bvar 0) (.bvar 0) (nodeDomain k) tailType
      (.refl ctx (.const 0 []) (nodePi k) (familyHeadNodeTy k))
      (.refl ctx (.bvar 0) (nodeDomain k) (argumentNodeTy k)))
    (.refl ctx (.bvar 0) (.sort .zero) propVarTy)

/-- Fixed Π endpoints, independent of the size of the derived application node. -/
def outerPi : Expr Nat := .pi familyApp (.bvar 1)

def outerPiTy (k : Nat) :
    HasTyT andEnvU 0 ctx outerPi (.sort (.imax .zero .zero)) :=
  .pi ctx familyApp .zero (.bvar 1) .zero (familyAppNodeTy k) (.bvar _ 1 _ rfl)

/-- The family-spine application occurs as the domain-conversion subderivation
of the Π comparison whose endpoints will be read off. -/
def outerPiConv (k : Nat) :
    TyConvT andEnvU 0 ctx outerPi outerPi :=
  .of ctx outerPi outerPi (.imax .zero .zero)
    (.pi ctx familyApp familyApp (.bvar 1) (.bvar 1) .zero .zero
      (familyAppNodeConv k) (.refl _ (.bvar 1) (.sort .zero) (.bvar _ 1 _ rfl)))

/-- A finite second proof of the seed's β conversion. Its argument typing
contains `firstAppTy 0`, whose head has been cast with `declaredToNode 0`.
There is no recursively defined derivation here. -/
def reentryDomainConv : ConvT andEnvU 0 ctx seedDomain (.sort .zero)
    (.sort (.succ .zero)) :=
  .beta ctx (.sort .zero) (.sort .zero) familyApp (.sort (.succ .zero))
    (.succ .zero) (.sort ctx .zero) (.sort _ .zero) (familyAppNodeTy 0)

/-- The outer Π conversion has exactly the endpoints of the alignment needed
by application inversion INSIDE the β argument typing above. -/
def reentryPiConv : TyConvT andEnvU 0 ctx (nodePi 0) andFamMember.mtype :=
  .of ctx (nodePi 0) andFamMember.mtype andFamSortU
    (.pi ctx (nodeDomain 0) (.sort .zero) tailType tailType
      (.succ .zero) (.imax (.succ .zero) (.succ .zero)) reentryDomainConv
      (.refl _ tailType (.sort (.imax (.succ .zero) (.succ .zero)))
        (.pi _ _ _ _ _ (.sort _ .zero) (.sort _ .zero))))

/-- Read the node from the EXACT application typing consumed by
`reentryDomainConv`: invert its two applications with the landed API. -/
def reentryRequest : Expr Nat × Expr Nat :=
  let lastApp := hasTyTInv_app (familyAppNodeTy 0) rfl
  let firstApp := hasTyTInv_app lastApp.2.2.1 rfl
  (.pi firstApp.1 firstApp.2.1, andFamMember.mtype)

theorem reentryRequest_eq :
    reentryRequest = (nodePi 0, andFamMember.mtype) := rfl

/-- No strictly decreasing natural rank of endpoint pairs can pay this direct
inversion request. A rank of DERIVATIONS or a validated replacement request is
not addressed: the original head conversion occurs inside the outer proof. -/
theorem reentry_no_strict_endpoint_rank (rank : Expr Nat × Expr Nat → Nat) :
    ¬ rank reentryRequest < rank (nodePi 0, andFamMember.mtype) := by
  rw [reentryRequest_eq]
  exact Nat.lt_irrefl _

theorem nodeDomain_size (k : Nat) : esize (nodeDomain k) = 9 + 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [nodeDomain, esize, ih]
      omega

theorem nodePi_size (k : Nat) : esize (nodePi k) = 13 + 4 * k := by
  simp only [nodePi, esize, tailType, nodeDomain_size]
  omega

theorem outerPi_size : esize outerPi = 7 := rfl

/-- The required node comparison is not smaller than even the sum of the two
outer Π endpoints, as soon as one identity β wrapper is added. -/
theorem nodePi_not_smaller (k : Nat) :
    ¬ esize (nodePi (k + 1)) < esize outerPi + esize outerPi := by
  rw [nodePi_size, outerPi_size]
  omega

theorem nodePi_unbounded (bound : Nat) :
    ∃ k, bound < esize (nodePi k) := by
  refine ⟨bound, ?_⟩
  rw [nodePi_size]
  omega

/-- The stored type really is a closed earlier-admitted declaration. -/
theorem declared_closed : exprClosedAt 0 andFamMember.mtype = true := rfl

theorem declared_no_constants (r : Nat) :
    occursConst r andFamMember.mtype = false := rfl

theorem nodeDomain_mentions_current_family (k : Nat) :
    occursConst 0 (nodeDomain k) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [nodeDomain, occursConst, Bool.false_or, ih]

theorem nodePi_mentions_current_family (k : Nat) :
    occursConst 0 (nodePi k) = true := by
  simp only [nodePi, occursConst, nodeDomain_mentions_current_family, Bool.true_or]

/-- The derived node fails the very support obligation needed to replay its
alignment strictly before the family's declaration at reference `0`. -/
theorem nodePi_not_strictly_earlier (k : Nat) :
    ¬ (∀ r, occursConst r (nodePi k) = true → r < 0) := by
  intro h
  exact Nat.not_lt_zero 0 (h 0 (nodePi_mentions_current_family k))

/-- The landed strengthening API exposes the missing hypothesis precisely:
the actual alignment chain is not `cleanTyConvT` below the current family.
This does not assert that no other derivation or model can establish alignment. -/
theorem nodeToDeclared_not_clean (k : Nat) :
    ¬ cleanTyConvT 0 (nodeToDeclared k) := by
  intro h
  exact Nat.not_lt_zero 0 (Rcic.Scm.SrcG.lt_of_constsBelow (nodePi k)
    (cleanTyConvT_node h).1 (nodePi_mentions_current_family k))

/-- More strongly, no derivation of this same alignment exists in the earlier
empty environment. A real conversion types its left endpoint, hence requires
the family at reference `0`; a pure-reflexivity chain has unequal endpoints. -/
theorem no_alignment_in_earlier_environment (k : Nat) :
    ¬ Nonempty (TyConvT emptyEnv 0 ctx (nodePi k) andFamMember.mtype) := by
  rintro ⟨h⟩
  rcases h.firstOf with he | ⟨C, u, ⟨hc⟩, _⟩
  · have hs := congrArg esize he
    have hn := nodePi_size k
    have hd : esize andFamMember.mtype = 5 := rfl
    omega
  · have hctx : CtxWfT emptyEnv 0 ctx :=
      .assumption [] (.sort .zero) (.succ .zero) .nil (.sort [] .zero)
    obtain ⟨⟨ht⟩, _⟩ := convT_endpoints EnvWfT.empty hctx hc
    obtain ⟨m, hm⟩ := member_of_occursConst (nodePi k)
      (hasTyT_constsIn ht) (nodePi_mentions_current_family k)
    cases hm

/-- Kernel-checkable joint witness: admitted environment and context, real
applications and Π conversion, an unbounded derived node, and no earlier support.
No premise is a Π-injectivity row or a semantic soundness claim. -/
theorem admitted_measure_obstruction (bound : Nat) :
    Nonempty (EnvWfT andEnvU) ∧ Nonempty (CtxWfT andEnvU 0 ctx) ∧
    ∃ k, Nonempty (HasTyT andEnvU 0 ctx familyApp (.sort .zero)) ∧
      Nonempty (HasTyT andEnvU 0 ctx (.const 0 []) (nodePi k)) ∧
      Nonempty (TyConvT andEnvU 0 ctx (nodePi k) andFamMember.mtype) ∧
      Nonempty (TyConvT andEnvU 0 ctx outerPi outerPi) ∧
      bound < esize (nodePi k) ∧
      ¬ (∀ r, occursConst r (nodePi k) = true → r < 0) := by
  obtain ⟨k, hk⟩ := nodePi_unbounded bound
  exact ⟨⟨andEnvUWfT⟩, ⟨ctxWf⟩, k, ⟨familyAppNodeTy k⟩,
    ⟨familyHeadNodeTy k⟩, ⟨nodeToDeclared k⟩, ⟨outerPiConv k⟩,
    hk, nodePi_not_strictly_earlier k⟩

end Rcic.Declarative.NativePiCycleMeasure

-- BEGIN ROOTS
#print axioms Rcic.Declarative.NativePiCycleMeasure.ctx
#print axioms Rcic.Declarative.NativePiCycleMeasure.ctxWf
#print axioms Rcic.Declarative.NativePiCycleMeasure.propVarTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyApp
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomain
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomainTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.seedDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomainTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.tailType
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi
#print axioms Rcic.Declarative.NativePiCycleMeasure.declaredToNode
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeToDeclared
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyHeadNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.argumentNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.firstAppTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.firstApp_inv_domain
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppNodeTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.familyAppNodeConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPi
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPiTy
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPiConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryDomainConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryPiConv
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryRequest
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentryRequest_eq
#print axioms Rcic.Declarative.NativePiCycleMeasure.reentry_no_strict_endpoint_rank
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.outerPi_size
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_not_smaller
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_unbounded
#print axioms Rcic.Declarative.NativePiCycleMeasure.declared_closed
#print axioms Rcic.Declarative.NativePiCycleMeasure.declared_no_constants
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeDomain_mentions_current_family
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_mentions_current_family
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodePi_not_strictly_earlier
#print axioms Rcic.Declarative.NativePiCycleMeasure.nodeToDeclared_not_clean
#print axioms Rcic.Declarative.NativePiCycleMeasure.no_alignment_in_earlier_environment
#print axioms Rcic.Declarative.NativePiCycleMeasure.admitted_measure_obstruction
-- END ROOTS
