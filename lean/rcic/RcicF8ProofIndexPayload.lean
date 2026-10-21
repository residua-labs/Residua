import rcic.RcicF8Ev
import rcic.RcicProofOccurrences

/-!
# Original-evidence payload for the single owner-side EvPar.proofIndex
Every judgment field is B2 provenance over the same root bundle. Materialized
endpoints are never relabeled as literal leaves. The direct irr payload uses
exactly its three original child typings; its lazy answer is refl. This module
certifies the unchanged proof-index producer, not a general J. closure_claim=0.
-/
namespace Rcic.Declarative.F8Measure
open F8Occurrences
variable {E : ResolvedEnv} {n : Nat}

structure ProofIndexPayload (R : List (Jd E n))
    (Γ : LCtx) (a b T : Expr Nat) where
  proposition : Expr Nat
  propTy : EvTy R Γ proposition (.sort .zero)
  chain : EvTc R Γ T proposition
  leftTy : EvTy R Γ a T
  rightTy : EvTy R Γ b T

variable {R : List (Jd E n)} {Γ : LCtx} {a b T : Expr Nat}

def ProofIndexPayload.leaves (p : ProofIndexPayload R Γ a b T) : List (Jd E n) :=
  p.propTy.leaves ++ p.chain.leaves ++ p.leftTy.leaves ++ p.rightTy.leaves

def ProofIndexPayload.size (p : ProofIndexPayload R Γ a b T) : Nat :=
  1 + p.propTy.size + p.chain.size + p.leftTy.size + p.rightTy.size

theorem ProofIndexPayload.leaves_root (p : ProofIndexPayload R Γ a b T)
    (x : Jd E n) (hx : x ∈ p.leaves) : ∃ r ∈ R, SubEq x r := by
  change x ∈ ((p.propTy.leaves ++ p.chain.leaves) ++ p.leftTy.leaves)
    ++ p.rightTy.leaves at hx
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact p.propTy.leaves_root x hx
      · exact p.chain.leaves_root x hx
    · exact p.leftTy.leaves_root x hx
  · exact p.rightTy.leaves_root x hx

/-- The index is tied to the OLD producer's actual output. -/
def ProofIndexPayload.requests (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (p : ProofIndexPayload R Γ a b T) :
    Requests (.peq Γ a b T
      (peqLeafT_reconcile_propIndex (p.propTy.val hcl hinst)
        (p.chain.val hcl hinst) (p.leftTy.val hcl hinst)
        (p.rightTy.val hcl hinst)).1) :=
  rootRequests (p.propTy.val hcl hinst) (p.chain.val hcl hinst)
    (p.leftTy.val hcl hinst) (p.rightTy.val hcl hinst)

def ProofIndexPayload.answers (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (p : ProofIndexPayload R Γ a b T) :
    AnsweredOrigins (.peq Γ a b T
      (peqLeafT_reconcile_propIndex (p.propTy.val hcl hinst)
        (p.chain.val hcl hinst) (p.leftTy.val hcl hinst)
        (p.rightTy.val hcl hinst)).1) (p.requests hcl hinst) :=
  rootAnswers (p.propTy.val hcl hinst) (p.chain.val hcl hinst)
    (p.leftTy.val hcl hinst) (p.rightTy.val hcl hinst)

def ProofIndexPayload.lazyAnswer (p : ProofIndexPayload R Γ a b T)
    (_side : Side) : EvTc R Γ T p.proposition := p.chain

theorem ProofIndexPayload.request_index (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (p : ProofIndexPayload R Γ a b T)
    (side : Side) : (p.requests hcl hinst PUnit.unit side).index = T := by
  cases side <;> rfl

theorem ProofIndexPayload.answer_materializes (hcl : EnvClosed E)
    (hinst : EnvMembersSubstStable E) (p : ProofIndexPayload R Γ a b T)
    (side : Side) :
    HEq (p.answers hcl hinst PUnit.unit side)
      ((p.lazyAnswer side).val hcl hinst) := by
  cases side <;> rfl

theorem ProofIndexPayload.lazyAnswer_leaves
    (p : ProofIndexPayload R Γ a b T) (side : Side) :
    (p.lazyAnswer side).leaves = p.chain.leaves := rfl

/-- Only widen B2 inputs; never inject a materialized output as lit. -/
def ProofIndexPayload.widen {R' : List (Jd E n)}
    (hr : ∀ x ∈ R, x ∈ R') (p : ProofIndexPayload R Γ a b T) :
    ProofIndexPayload R' Γ a b T where
  proposition := p.proposition
  propTy := p.propTy.widen hr
  chain := p.chain.widen hr
  leftTy := p.leftTy.widen hr
  rightTy := p.rightTy.widen hr

theorem ProofIndexPayload.leaves_widen {R' : List (Jd E n)}
    (hr : ∀ x ∈ R, x ∈ R') (p : ProofIndexPayload R Γ a b T) :
    (p.widen hr).leaves = p.leaves := by
  simp only [ProofIndexPayload.widen, ProofIndexPayload.leaves,
    EvTy.leaves_widen, EvTc.leaves_widen]

section LiteralIrr
variable {P p q : Expr Nat}

/-- Three ORIGINAL ConvT.irr children; no reconstructed endpoint is admitted. -/
def literalIrrPayload
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    ProofIndexPayload [Jd.cv (.irr Γ P p q hP hp hq)] Γ p q P where
  proposition := P
  propTy := .lit hP ⟨_, .head _, .inr (.child (.head _))⟩
  chain := .refl Γ P
  leftTy := .lit hp ⟨_, .head _, .inr (.child (.tail _ (.head _)))⟩
  rightTy := .lit hq ⟨_, .head _, .inr (.child (.tail _ (.tail _ (.head _))))⟩

theorem literalIrrPayload_leaves
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    (literalIrrPayload hP hp hq).leaves = [Jd.ty hP, Jd.ty hp, Jd.ty hq] := rfl

theorem literalIrrPayload_strict
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P)
    (x : Jd E n) (hx : x ∈ (literalIrrPayload hP hp hq).leaves) :
    SubOf x (Jd.cv (.irr Γ P p q hP hp hq)) := by
  apply SubOf.child
  change x ∈ [Jd.ty hP, Jd.ty hp, Jd.ty hq]
  exact hx

/-- This original-root replacement is strict. It does not authorize an
arbitrary later consumer to re-ask on the materialized result. -/
theorem literalIrrPayload_dm
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    Rcic.Syn.DMStep ((literalIrrPayload hP hp hq).leaves.map Jd.wt)
      ([Jd.cv (.irr Γ P p q hP hp hq)].map Jd.wt) := by
  simpa only [List.append_nil] using
    (dm_of_strictLeaves (X := [Jd.cv (.irr Γ P p q hP hp hq)])
      (Z := []) (L := (literalIrrPayload hP hp hq).leaves)
      (List.cons_ne_nil _ _)
      (fun x hx => ⟨_, .head _, literalIrrPayload_strict hP hp hq x hx⟩))

theorem literalIrr_no_self_request
    (hP : HasTyT E n Γ P (.sort .zero))
    (hp : HasTyT E n Γ p P) (hq : HasTyT E n Γ q P) :
    ¬ SubOf (Jd.cv (.irr Γ P p q hP hp hq))
      (Jd.cv (.irr Γ P p q hP hp hq)) := subOf_irrefl _
end LiteralIrr
end Rcic.Declarative.F8Measure
