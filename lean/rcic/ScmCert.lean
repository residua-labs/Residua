import rcic.ScmEvidence

/-!
# CT-018 — closed / hybrid certificates

07 §18: `ClosedReflectiveCertificate | HybridCertificate`. Both bind
the exact bound subject, annotations, VC bundle, and evidence bytes.
07 §16: the checker requires the VC vector **exact** — no missing,
extra, reordered, or substitute VC.

`CertBundle` binds `subject`/`annotations` parametrically — the bound
subject is the certCheck carrier's object; this layer binds it exactly
by the field itself. `certValid` = evidence covers the VC bundle
exactly and in order (`evs.map Sigma.fst = vcs`) + every member valid.

Teeth pin each refusal arm of the exactness: shorter, longer,
different (substitute/reordered) coverage lists, an invalid member
anywhere, and a non-reflected member inside a closed certificate.
-/

namespace Rcic.Scm.Cert
open Rcic.Scm.Reflect Rcic.Scm.Evidence

/-- §18 certificate bundle: the bound subject, the annotations, the VC
    bundle, and the evidence bytes — each evidence pack indexed by the
    exact VC it is for. `S`/`A` are parametric: the concrete bound
    subject and annotation objects are the certCheck carrier's data;
    here the binding is the field itself. -/
structure CertBundle (S A : Type) where
  subject : S
  annotations : A
  vcs : List VC
  evs : List (Σ vc, VCEvidence vc)

/-- Certificate validity (§16 exactness + §18 evidence soundness): the
    evidence list covers the VC bundle **exactly and in order** — no
    missing, extra, reordered, or substitute VC — and every member's
    evidence is valid. -/
def certValid {S A} (c : CertBundle S A) : Prop :=
  c.evs.map Sigma.fst = c.vcs ∧ ∀ e ∈ c.evs, evValid e.2

/-- §18 `ClosedReflectiveCertificate`: a valid bundle whose evidence
    is all of the `reflected` kind. -/
def ClosedReflectiveCertificate {S A} (c : CertBundle S A) : Prop :=
  certValid c ∧ ∀ e ∈ c.evs, e.2.isReflected = true

/-- §18 `HybridCertificate`: a valid bundle — evidence kinds may mix. -/
def HybridCertificate {S A} (c : CertBundle S A) : Prop :=
  certValid c

/-- **CT-018.** A valid certificate discharges every bound VC: each
    VC's denotation holds in its own pinned environment. -/
theorem cert_sound {S A} {c : CertBundle S A} (hv : certValid c) :
    ∀ vc ∈ c.vcs, denoteProp vc.prop vc.env vc.penv := by
  intro vc hvc
  obtain ⟨hcov, hval⟩ := hv
  have hm : vc ∈ c.evs.map Sigma.fst := hcov ▸ hvc
  obtain ⟨e, he, hfe⟩ := List.mem_map.mp hm
  have hvld : evValid e.2 := hval _ he
  subst hfe
  exact evidence_sound e.2 hvld

/-- Closed certificates are sound — the CT-018 closed arm. -/
theorem closed_cert_sound {S A} {c : CertBundle S A}
    (h : ClosedReflectiveCertificate c) :
    ∀ vc ∈ c.vcs, denoteProp vc.prop vc.env vc.penv :=
  cert_sound h.1

/-- Hybrid certificates are sound — the CT-018 hybrid arm. -/
theorem hybrid_cert_sound {S A} {c : CertBundle S A}
    (h : HybridCertificate c) :
    ∀ vc ∈ c.vcs, denoteProp vc.prop vc.env vc.penv :=
  cert_sound h

/-! ## Teeth -/

/-- Missing VC: fewer evidence packs than bound VCs is refused —
    coverage is exact, not a prefix. -/
theorem cert_missing_vc_refused {S A} {c : CertBundle S A}
    (h : c.evs.length < c.vcs.length) : ¬ certValid c := by
  rintro ⟨hcov, -⟩
  have hl := congrArg List.length hcov
  rw [List.length_map] at hl
  omega

/-- Extra evidence is refused — coverage is exact, not a superset. -/
theorem cert_extra_evidence_refused {S A} {c : CertBundle S A}
    (h : c.vcs.length < c.evs.length) : ¬ certValid c := by
  rintro ⟨hcov, -⟩
  have hl := congrArg List.length hcov
  rw [List.length_map] at hl
  omega

/-- Substitute or reordered coverage: if the evidence's bound-VC list
    is not the bundle's VC list exactly, refused — a proof of a
    different proposition is not evidence for this VC. -/
theorem cert_diff_vc_refused {S A} {c : CertBundle S A}
    (h : c.evs.map Sigma.fst ≠ c.vcs) : ¬ certValid c :=
  fun ⟨hc, _⟩ => h hc

/-- An invalid member anywhere in the evidence list is refused —
    covers the hybrid arm's mixed contents. -/
theorem cert_invalid_member_refused {S A} {c : CertBundle S A}
    {e : Σ vc, VCEvidence vc} (hm : e ∈ c.evs) (hv : ¬ evValid e.2) :
    ¬ certValid c :=
  fun ⟨_, hval⟩ => hv (hval _ hm)

/-- A bundle carrying any non-reflected evidence is not a closed
    certificate — the closed/hybrid split is on evidence kind. -/
theorem not_closed_of_nonreflected {S A} {c : CertBundle S A}
    {e : Σ vc, VCEvidence vc} (hm : e ∈ c.evs)
    (hk : e.2.isReflected = false) :
    ¬ ClosedReflectiveCertificate c := fun ⟨_, hall⟩ => by
  have h := hall _ hm
  rw [hk] at h
  exact Bool.false_ne_true h

end Rcic.Scm.Cert
