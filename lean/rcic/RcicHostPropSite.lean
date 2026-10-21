import rcic.RcicProofOccurrences
import rcic.RcicHostPropTransfer

/-!
# piRow wall, piece A — the host-solved answer at an original proof site (§3.2)

Spec: `research/rcic/sortrow/PIROW_FAMAPPROW_FULL_ENVWFT.md` §3.2 (J line, #7515).
`SiteRequest.Answer` asks for a chain from the position's host index to the original
proposition (`RcicProofOccurrences`); host transfer does not prove that. The new conclusion for
an original site `s`, side, request `r` is `HostSolved r`: the host index is a proposition. It
is produced by `hostProp_of_isProof0` on `r.positionTyping` with the site's own original
certificate (`ProofSite.isProof`). The original `SiteRequest` is untouched — occurrence, side,
proposition metadata, host index, position typing are preserved; the proposition is not
relabelled. A host-solved request re-emits as a proof-peak root with the host as its proposition
(`P := r.index`, `hTP := TyConvT.refl`), so the landed generated-root request/answer machinery
applies unchanged (`hostRootRequests`, `hostRootAnswers`). The `PEqLeafT` leaf finish is the
§2.7 finish at the leaf's two retained common-host typings (`irr_of_peqLeafT0`).
`closure_claim = 0`.
-/
set_option autoImplicit false

namespace Rcic.Declarative.F8Occurrences

open Rcic.Declarative.HostProp
open Rcic.Declarative.F8A2Support (IsProof)

variable {E : ResolvedEnv} {n : Nat}

/-- §3.2 the proof consumer's new conclusion at an original site: the request's host index is a
    proposition. The request itself is the exact original one. -/
def HostSolved {s : ProofSite E n} {side : Side} (r : SiteRequest s side) : Prop :=
  Nonempty (HasTyT E n s.context r.index (.sort .zero))

/-- the site's own original certificate: `s.term side` is a proof of `s.proposition side`. -/
theorem ProofSite.isProof (s : ProofSite E n) :
    (side : Side) → IsProof E n s.context (s.term side)
  | .left => ⟨s.leftProp, ⟨s.leftPropTy⟩, ⟨s.leftTy⟩⟩
  | .right => ⟨s.rightProp, ⟨s.rightPropTy⟩, ⟨s.rightTy⟩⟩

/-- §3.2 producer: host transfer on `r.positionTyping` with the original certificate at `s`. -/
theorem hostSolved_of_site (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {s : ProofSite E n} (hΓ : CtxWfT E n s.context) {side : Side}
    (r : SiteRequest s side) : HostSolved r :=
  hostProp_of_isProof0 zsc hW r.positionTyping hΓ (s.isProof side)

/-- §2.7 at a `PEqLeafT` leaf: its two retained common-host typings and one external
    certificate close the leaf by `ConvT.irr` at the host. -/
theorem irr_of_peqLeafT0 (zsc : ZeroSortCoherence E n) (hW : EnvWfT E)
    {Γ : LCtx} (hΓ : CtxWfT E n Γ) {p q T P : Expr Nat} (leaf : PEqLeafT E n Γ p q T)
    (hpP : HasTyT E n Γ p P) (hP : HasTyT E n Γ P (.sort .zero)) :
    Nonempty (ConvT E n Γ p q T) :=
  irr_of_common_host0 zsc hW hΓ leaf.2.1 leaf.2.2 hpP hP

/-- §3.2 a host-solved request re-emitted as a proof-peak root with the host as its
    proposition (`P := r.index`, `hTP := TyConvT.refl`), given the host sorting as data and a
    second typing at the host: the landed root requests, unchanged. -/
def hostRootRequests {s : ProofSite E n} {side : Side} (r : SiteRequest s side)
    (hP : HasTyT E n s.context r.index (.sort .zero)) {b : Expr Nat}
    (hb : HasTyT E n s.context b r.index) :
    Requests (.peq s.context (s.term side) b r.index
      (peqLeafT_reconcile_propIndex hP (.refl _ r.index) r.positionTyping hb).1) :=
  rootRequests hP (.refl _ r.index) r.positionTyping hb

/-- the landed root answers at the host-rooted peak. -/
def hostRootAnswers {s : ProofSite E n} {side : Side} (r : SiteRequest s side)
    (hP : HasTyT E n s.context r.index (.sort .zero)) {b : Expr Nat}
    (hb : HasTyT E n s.context b r.index) :
    AnsweredOrigins (.peq s.context (s.term side) b r.index
      (peqLeafT_reconcile_propIndex hP (.refl _ r.index) r.positionTyping hb).1)
      (hostRootRequests r hP hb) :=
  rootAnswers hP (.refl _ r.index) r.positionTyping hb

end Rcic.Declarative.F8Occurrences

#print axioms Rcic.Declarative.F8Occurrences.ProofSite.isProof
#print axioms Rcic.Declarative.F8Occurrences.hostSolved_of_site
#print axioms Rcic.Declarative.F8Occurrences.irr_of_peqLeafT0
#print axioms Rcic.Declarative.F8Occurrences.hostRootRequests
#print axioms Rcic.Declarative.F8Occurrences.hostRootAnswers
