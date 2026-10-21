import rcic.ScmCert
import rcic.ScmReflectPins

/-!
# CT-017/018 pins — evidence and certificates on concrete VCs

Fixtures reuse the CT-012 corpus (`penv0`/`penv1`/`env5`, `r08_den`).
Pins exercise: reflected + typedProofTerm evidence, `envExact` on a
nonempty context, a closed reflective certificate, a hybrid
certificate, and every refusal arm — false-prop evidence, padded env,
name-only pack, missing/extra/reordered/substitute coverage, invalid
member, non-reflected member inside a closed cert.
-/

namespace Rcic.Scm.Evidence.Pins
open Rcic.Scm.Reflect Rcic.Scm.Reflect.Pins Rcic.Scm.Evidence Rcic.Scm.Cert

/-! ## VC fixtures -/

/-- `3 = 3` in the empty env — defined-true, `reflected`-decidable. -/
def vc1 : VC := ⟨[], .eq (.litI 3) (.litI 3), [], penv0⟩
/-- `pos(4)` under `penv1` — defined-true predicate call. -/
def vc2 : VC := ⟨[], .pcall "pos" [⟨.int, .litI 4⟩], [], penv1⟩
/-- `x₀ = 5` at `Γ = [.int]`, `env5` — nonempty exact env. -/
def vc3 : VC := ⟨[.int], .eq (.var 0 rfl) (.litI 5), env5, penv0⟩
/-- `3 = 4` in the empty env — defined-false; no valid reflected
    evidence exists. -/
def vcF : VC := ⟨[], .eq (.litI 3) (.litI 4), [], penv0⟩
/-- `x₀ = 5` at `Γ = [.int]` in a **padded** env — `envExact` fails. -/
def vcPad : VC := ⟨[.int], .eq (.var 0 rfl) (.litI 5), ⟨.int, 5⟩ :: env5, penv0⟩

/-! ## Evidence validity pins -/

/-- The exact minimal env at `Γ = [.int]`, `env5`. -/
theorem envExact_v3 : envExact vc3.Γ vc3.env := ⟨rfl, trivial⟩

theorem ev_v1 : evValid (.reflected : VCEvidence vc1) := ⟨trivial, by decide⟩
theorem ev_v3 : evValid (.reflected : VCEvidence vc3) := ⟨envExact_v3, by decide⟩
theorem ev_v3_pt :
    evValid (.typedProofTerm r08_den : VCEvidence vc3) := envExact_v3

/-- CT-017 at a pin: valid reflected evidence yields the denotation. -/
theorem ev_v1_sound : denoteProp vc1.prop vc1.env vc1.penv :=
  evidence_sound _ ev_v1
/-- CT-017 at a pin: a typed proof term yields the denotation. -/
theorem ev_v3_pt_sound : denoteProp vc3.prop vc3.env vc3.penv :=
  evidence_sound _ ev_v3_pt

/-- Tooth: reflected evidence on a defined-false VC is refused. -/
theorem ev_false_refused : ¬ evValid (.reflected : VCEvidence vcF) :=
  reflected_invalid_of_decide_ne (by decide)

/-- Tooth: a padded env is not the exact minimal env — evidence
    refused. -/
theorem ev_padded_refused : ¬ evValid (.reflected : VCEvidence vcPad) := by
  rintro ⟨hx, -⟩
  exact hx.2

/-- Tooth: a bare name/q pack is never valid evidence — §18's "a
    theorem name or proof q alone is insufficient". -/
theorem named_pack_refused :
    ¬ evValidM (.named "q_deadbeef" : VCEvidenceM vc1) :=
  named_never_valid

/-! ## Certificate pins -/

/-- A closed reflective certificate: two VCs, both `reflected`. -/
def certClosed : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vc2]
  evs := [⟨vc1, .reflected⟩, ⟨vc2, .reflected⟩]

theorem certClosed_valid : certValid certClosed := by
  refine ⟨rfl, ?_⟩
  intro e he
  simp only [certClosed, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · exact ev_v1
  · exact ⟨trivial, by decide⟩

theorem certClosed_closed : ClosedReflectiveCertificate certClosed :=
  ⟨certClosed_valid, fun e he => by
    simp only [certClosed, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl <;> rfl⟩

/-- CT-018 closed arm at a pin: every bound VC's denotation holds. -/
theorem certClosed_sound :
    ∀ vc ∈ certClosed.vcs, denoteProp vc.prop vc.env vc.penv :=
  closed_cert_sound certClosed_closed

/-- A hybrid certificate: one `reflected`, one `typedProofTerm`. -/
def certHybrid : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vc3]
  evs := [⟨vc1, .reflected⟩, ⟨vc3, .typedProofTerm r08_den⟩]

theorem certHybrid_valid : certValid certHybrid := by
  refine ⟨rfl, ?_⟩
  intro e he
  simp only [certHybrid, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    or_false] at he
  rcases he with rfl | rfl
  · exact ev_v1
  · exact ev_v3_pt

/-- CT-018 hybrid arm at a pin. -/
theorem certHybrid_sound :
    ∀ vc ∈ certHybrid.vcs, denoteProp vc.prop vc.env vc.penv :=
  hybrid_cert_sound certHybrid_valid

/-- Tooth: a bundle carrying a `typedProofTerm` is not a closed
    certificate. -/
theorem certHybrid_not_closed : ¬ ClosedReflectiveCertificate certHybrid :=
  not_closed_of_nonreflected
    (e := ⟨vc3, .typedProofTerm r08_den⟩)
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) rfl

/-- Tooth: missing coverage (one VC, no evidence) is refused. -/
def certMissing : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vc2]
  evs := [⟨vc1, .reflected⟩]

theorem cert_missing_refused_pin : ¬ certValid certMissing :=
  cert_missing_vc_refused (by decide)

/-- Tooth: extra evidence beyond the bundle is refused. -/
def certExtra : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vc2]
  evs := [⟨vc1, .reflected⟩, ⟨vc2, .reflected⟩,
          ⟨vc3, .typedProofTerm r08_den⟩]

theorem cert_extra_refused_pin : ¬ certValid certExtra :=
  cert_extra_evidence_refused (by decide)

/-- Tooth: the same packs in swapped order do not cover — coverage is
    ordered, not a set match. -/
def certReordered : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vc2]
  evs := [⟨vc2, .reflected⟩, ⟨vc1, .reflected⟩]

theorem cert_reorder_refused : ¬ certValid certReordered := by
  rintro ⟨hcov, -⟩
  have hm : [vc2, vc1] = [vc1, vc2] := hcov
  have h1 : vc2 = vc1 := (List.cons.inj hm).1
  have hp : vc2.penv = vc1.penv := congrArg VC.penv h1
  have hq : penv1 "pos" = penv0 "pos" := congrFun hp "pos"
  exact Option.noConfusion hq

/-- Tooth: evidence for a different VC than the bound one is refused —
    a proof of a different proposition is not evidence for this VC. -/
def certSubst : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vcF]
  evs := [⟨vc1, .reflected⟩, ⟨vc2, .reflected⟩]

theorem cert_substitute_refused : ¬ certValid certSubst := by
  rintro ⟨hcov, -⟩
  have hm : [vc1, vc2] = [vc1, vcF] := hcov
  have h2 : [vc2] = [vcF] := (List.cons.inj hm).2
  have h3 : vc2 = vcF := (List.cons.inj h2).1
  have hp : vc2.penv = vcF.penv := congrArg VC.penv h3
  have hq : penv1 "pos" = penv0 "pos" := congrFun hp "pos"
  exact Option.noConfusion hq

/-- Tooth: coverage exact but a member invalid — refused. -/
def certBadMember : CertBundle Unit Unit where
  subject := ()
  annotations := ()
  vcs := [vc1, vcF]
  evs := [⟨vc1, .reflected⟩, ⟨vcF, .reflected⟩]

theorem cert_badmember_refused : ¬ certValid certBadMember :=
  cert_invalid_member_refused
    (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ev_false_refused

end Rcic.Scm.Evidence.Pins
