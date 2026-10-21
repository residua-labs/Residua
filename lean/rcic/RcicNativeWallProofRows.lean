import rcic.RcicNativeWallHostProp
import rcic.RcicNativeWallProofSource

/-!
# Constructed proof-source rows with the zero-sort premise exposed

These compose the actual data-valued host transfer with the source-centre
joins. `ZeroSortCoherence` remains an explicit hypothesis. No declaration
here supplies the nonproof computational rows or the global diamond.

Dependency pin: `4d3b74e05355f478a03a44166399794a0a68d2a4`.
`closure_claim = 0`.
-/

namespace Rcic.Declarative.NativeValleys

variable {E : ResolvedEnv} {n : Nat}
variable {PEq : LCtx → Expr Nat → Expr Nat → Expr Nat → Type}

def join_proof_source_of_zero_sort (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hbP : HasTyT E n Γ b P)
    (p : CStep E n PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  ProofSourceAudit.join_of_proof_source L
    (HostPropAudit.hostPropData_of_zeroSortCoherence hW zsc) hΓ hP hbP p q

def join_peq_source_of_zero_sort (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d e T₁ T₂ : Expr Nat}
    (h : PEq Γ b d T₁) (q : CStep E n PEq Γ b e T₂) :
    Σ' (f : Expr Nat), CStep E n PEq Γ d f T₁ ×' CStep E n PEq Γ e f T₂ :=
  ProofSourceAudit.join_peq_source L
    (HostPropAudit.hostPropData_of_zeroSortCoherence hW zsc) hΓ h q

/-- In an application peak whose function is externally known to be a proof,
one actual function/argument typing suffices to witness proofhood of the
whole source. No comparison with the other input's Pi data is requested. -/
def join_application_of_proof_function (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {f a A B P d e T₁ T₂ : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hfP : HasTyT E n Γ f P)
    (hf : HasTyT E n Γ f (.pi A B)) (ha : HasTyT E n Γ a A)
    (p : CStep E n PEq Γ (.app f a) d T₁)
    (q : CStep E n PEq Γ (.app f a) e T₂) :
    Σ' (g : Expr Nat), CStep E n PEq Γ d g T₁ ×' CStep E n PEq Γ e g T₂ :=
  let hPi0 := HostPropAudit.hostPropData_of_zeroSortCoherence hW zsc hΓ hf hP hfP
  let hB0 := HostPropAudit.pi_codomain_prop_data hW zsc hΓ hPi0
  let hRes0 := hasTyT_subst0S (envClosed_of_envWfT hW)
    (envMembersSubstStable_of_envWfT hW) hB0 ha
  join_proof_source_of_zero_sort hW L zsc hΓ hRes0 (.app Γ f a A B hf ha) p q

def valley_proof_source_of_zero_sort (hW : EnvWfT E) (L : LeafIface E n PEq)
    (zsc : HostPropAudit.ZeroSortCoherence E n)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {b d T P : Expr Nat}
    (hP : HasTyT E n Γ P (.sort .zero)) (hbP : HasTyT E n Γ b P)
    (c : ConvT E n Γ b d T) : CValley E n PEq Γ b d T :=
  ProofSourceAudit.valley_of_proof_source hW L
    (HostPropAudit.hostPropData_of_zeroSortCoherence hW zsc) hΓ hP hbP c

#print axioms join_proof_source_of_zero_sort
#print axioms join_peq_source_of_zero_sort
#print axioms join_application_of_proof_function
#print axioms valley_proof_source_of_zero_sort

end Rcic.Declarative.NativeValleys
