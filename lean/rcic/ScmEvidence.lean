import rcic.ScmReflect

/-!
# CT-017 — VC evidence: `VCEvidence` reflected / typedProofTerm

07 §18: `VCEvidence := reflected | typedProofTerm`. Reflected evidence
uses the assertion decision theorem (CT-012's `decideProp_iff`);
typed proof evidence carries actual proof bytes checked at the exact
VC proposition in the exact minimal environment — a theorem name or
proof q alone is insufficient.

Here a `VC` is an `AssertProp` together with the exact environment it
must hold in. `VCEvidence vc` is indexed by the exact VC — evidence is
always *at* its proposition, never ambient. `envExact` is "the exact
minimal environment": exactly the context's entries, each tagged with
its declared type — nothing ambient, nothing missing.

`typedProofTerm`'s proof bytes are a typed proof term of the exact
denoted proposition (`h : denoteProp …`): inhabitation at that
proposition in that environment *is* the check — the kernel did it,
and a name or q alone cannot inhabit it. The byte-level checker of
the scm carrier (grok C's certCheck leg) is its own object; this file
models the semantics both evidence kinds must satisfy.

Teeth: `reflected_invalid_of_decide_ne` (decide ≠ true ⇒ no valid
reflected evidence, covering defined-false and undefined alike),
`envExact_padded_refused` (padded env is not minimal), and the
`VCEvidenceM` mutant whose `named` arm is the §18-forbidden shape —
admitted by the grammar, refused by validity.
-/

namespace Rcic.Scm.Evidence
open Rcic.Scm.Reflect

/-- A verification condition: a proposition together with the exact
    environment it must hold in. -/
structure VC where
  Γ : ACtx
  prop : AssertProp Γ
  env : AEnv
  penv : PredEnv

/-- The exact minimal environment: `e` has exactly Γ's entries, each
    tagged with the declared type. The structural match forces the same
    length — a padded or short env is not exact. -/
def envExact : ACtx → AEnv → Prop
  | [], [] => True
  | T :: Γ, x :: e => x.1 = T ∧ envExact Γ e
  | _, _ => False

/-- §18 `VCEvidence` — evidence for a VC, indexed by the exact VC. -/
inductive VCEvidence (vc : VC) where
  /-- Reflected evidence: the deciding bit on the exact VC
      proposition in the exact minimal env is the whole payload. -/
  | reflected
  /-- Typed proof evidence: a typed proof term of the exact denoted
      proposition — proof bytes, not a reference. -/
  | typedProofTerm (h : denoteProp vc.prop vc.env vc.penv)

/-- The evidence-kind tag for the closed/hybrid certificate split. -/
def VCEvidence.isReflected {vc : VC} : VCEvidence vc → Bool
  | .reflected => true
  | .typedProofTerm _ => false

/-- Evidence validity. `reflected` is valid when the environment is
    the exact minimal one and `decideProp` answers `true` there;
    `typedProofTerm` is valid when the environment is exact — its `h`
    is already a checked proof term at the exact proposition. -/
def evValid {vc : VC} : VCEvidence vc → Prop
  | .reflected =>
    envExact vc.Γ vc.env ∧ decideProp vc.prop vc.env vc.penv = true
  | .typedProofTerm _ => envExact vc.Γ vc.env

/-- **CT-017.** Every valid evidence pack yields its VC's denotation:
    `reflected` via `decideProp_iff` (the soundness direction of
    CT-012), `typedProofTerm` via the checked term it carries. -/
theorem evidence_sound {vc : VC} (ev : VCEvidence vc) (hv : evValid ev) :
    denoteProp vc.prop vc.env vc.penv := by
  cases ev with
  | reflected =>
      obtain ⟨_, hd⟩ := hv
      exact (decideProp_iff _ _ _).mp hd
  | typedProofTerm h => exact h

/-! ## Teeth -/

/-- Refusal arm: `reflected` evidence on a VC the decider does not
    answer `true` on is never valid — defined-false and undefined
    (strict partiality) alike. -/
theorem reflected_invalid_of_decide_ne {vc : VC}
    (h : decideProp vc.prop vc.env vc.penv ≠ true) :
    ¬ evValid (.reflected : VCEvidence vc) :=
  fun ⟨_, hd⟩ => h hd

/-- An exact env's length is exactly Γ's. -/
theorem envExact_length {Γ : ACtx} {e : AEnv} (h : envExact Γ e) :
    e.length = Γ.length := by
  induction Γ generalizing e with
  | nil =>
      cases e with
      | nil => rfl
      | cons y e' => exact absurd h (by simp [envExact])
  | cons T Γ ih =>
      cases e with
      | nil => exact absurd h (by simp [envExact])
      | cons y e' =>
          obtain ⟨_, hx⟩ := h
          have h' := ih hx
          simp [h']

/-- Refusal arm: a padded environment is not the exact minimal
    environment — `envExact` forces the lengths equal. -/
theorem envExact_padded_refused {Γ : ACtx} {e : AEnv} {x : Sigma denTy}
    (h₁ : envExact Γ (x :: e)) (h₂ : envExact Γ e) : False := by
  have hl₁ := envExact_length h₁
  have hl₂ := envExact_length h₂
  simp at hl₁
  omega

/-- The mutant evidence grammar: §18's two arms **plus** a bare
    name/q arm — the shape §18 forbids ("a theorem name or proof q
    alone is insufficient"). The spec `VCEvidence` stays two-armed;
    the mutant exists to pin the refusal. -/
inductive VCEvidenceM (vc : VC) where
  | ofReflected
  | ofProofTerm (h : denoteProp vc.prop vc.env vc.penv)
  | named (q : String)

/-- Validity on the mutant grammar: identical on the two legal arms,
    definitional `False` on the name arm — a name carries nothing the
    check could succeed on. -/
def evValidM {vc : VC} : VCEvidenceM vc → Prop
  | .ofReflected =>
    envExact vc.Γ vc.env ∧ decideProp vc.prop vc.env vc.penv = true
  | .ofProofTerm _ => envExact vc.Γ vc.env
  | .named _ => False

/-- The name-alone tooth: a bare q pack is never valid evidence, in
    any VC, under any environment. -/
theorem named_never_valid {vc : VC} {q : String} :
    ¬ evValidM (.named q : VCEvidenceM vc) :=
  id

/-- The mutant stays sound — the name arm is vacuous under validity
    (`evValidM (.named q)` is `False`), so soundness holds on all of
    `VCEvidenceM`; the mutant's only divergence is that the name arm
    can never supply a validity hypothesis. -/
theorem evidence_soundM {vc : VC} (ev : VCEvidenceM vc) (hv : evValidM ev) :
    denoteProp vc.prop vc.env vc.penv := by
  cases ev with
  | ofReflected =>
      obtain ⟨_, hd⟩ := hv
      exact (decideProp_iff _ _ _).mp hd
  | ofProofTerm h => exact h
  | named q => exact False.elim hv

end Rcic.Scm.Evidence
