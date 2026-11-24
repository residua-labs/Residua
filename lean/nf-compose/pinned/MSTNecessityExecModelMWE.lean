/-!
# MST Necessity Execution Model MWE — P1-A + P1-B

This file defines the minimal execution model (`ExecModel`) for the
MST Necessity → MST-NF proof program.

P1-A proves:
1. `sameClass_sameOutcome`: the key R1 theorem — raw execution must
   factor through the quotient class; raw identity cannot influence outcome.
2. `execModel_with_all_roles_has_mstnf_profile`: a model satisfying all
   four structural properties has the MST-NF execution profile.

P1-B proves:
3. `semantics_factor_through_kernel_quotient`: any semantic interpretation
   that respects the MST quotient structure must factor uniquely through the
   kernel quotient. This is the universal property of the quotient —
   the mathematical meaning of "semantics is defined by structure".

Roles mapped:
  R1 distinguish  → quotientFactorization + sameClass_sameOutcome
  R2 constrain    → admissibilitySound
  Φ5 totality     → residueTotality
  Φ2b precision   → representativePrecision

Boundary: this is a finite MWE-layer type definition.  Uniqueness of
representatives is encoded by the function-nature of `sigma`; a
relational/list-valued model would be needed to make uniqueness
itself a nontrivial proof obligation.

P1-B boundary: `semantics_factor_through_kernel_quotient` is stated over the
kernel quotient `Quot (fun x y => q x = q y)` and uses no choice axiom:
`m_bar` is `Quot.lift m h` and uniqueness is proved by `Quot.inductionOn`.
The equivalent statement over the active image `{ c : Class // ∃ r, q r = c }`
is recoverable by composing with `rawKernelQuotientEquivActiveClass_classical`;
that equivalence is the only declaration in this file that uses
`Classical.choice` (its inverse direction must pick a representative out of a
`Prop`-level `∃`), and no theorem depends on it.

## Two-tier axiom structure

The MST-NF axiom system has two distinct tiers. This distinction is a
research finding, not a design choice — it was discovered by observing
that election safety and log safety require conditions that are
orthogonal to the four execution structure axioms below.

### Tier 1: Execution structure axioms (`hasMSTNFProfile`)

The four axioms bundled in `hasMSTNFProfile` answer the question:
**"How should execution be structured to be non-redundant and
well-formed?"** They describe the admissibility boundary of an
execution model:

  `quotientFactorization`    — outcome is determined by class, not raw identity
  `admissibilitySound`       — only admissible classes have representatives
  `residueTotality`          — every rejection has a named reason
  `representativePrecision`  — every admissible class has at least one representative

These axioms collectively ensure:
- Outcome uniformity (same class → same result)
- Role completeness (every role is populated)
- No silent failure (every rejection is explained)

What Tier 1 does NOT ensure: how many distinct raw events per class
are admitted. `representativePrecision` says "at least one exists";
it says nothing about whether more than one can pass.

### Tier 2: The fifth axiom — `AtMostOneAdmit`

**This is the formal record of the gap discovered in the MST-NF
axiom system.** Tier 1 cannot derive election safety. The missing
condition is `AtMostOneAdmit`, defined in this file:

  `AtMostOneAdmit` — at most one raw event per admissible class
                      (corresponds to election safety)

`AtMostOneAdmit` is orthogonal to all four Tier 1 axioms — neither
direction of implication holds between `AtMostOneAdmit` and any
individual Tier 1 axiom, and in particular:

  `representativePrecision` does NOT imply `AtMostOneAdmit`:
    `twoEltCollapse` witness — two distinct raw events q-collapse to
    one admissible class; `representativePrecision` holds (sigma exists)
    but `AtMostOneAdmit` fails (r1 ≠ r2 both map to same class).

  `AtMostOneAdmit` does NOT imply `representativePrecision`:
    `singletonNoSigma` witness — one raw event, vacuously at-most-one,
    but sigma = none violates `representativePrecision`.

Both counterexamples are proved in `MSTNFSafetyAxiomsMWE.lean`.

`hasMSTNFSafetyProfile` (defined below) bundles Tier 1 + Tier 2:
a model satisfying all five axioms guarantees both outcome uniformity
and admission uniqueness.

### Why the gap is real and intentional

Tier 1 describes *execution optimization*: what makes an execution
model non-redundant. The question is "which events can be collapsed
without changing the outcome?" This question does not ask how many
events are admitted per class — only that admitted classes are
well-formed.

Tier 2 (`AtMostOneAdmit`) describes *safety*: what the execution model
prevents. The question is "can two conflicting decisions both be
admitted?" This is a different question, with a different structural
answer.

The gap is not a defect. It is the formal boundary between two
distinct concerns that happen to share the same (q, a, σ, ρ)
vocabulary. MST-NF's contribution is making this boundary explicit
and machine-verifiable.
-/

namespace MSTNecessityExecModelMWE

-- ---------------------------------------------------------------------------
-- Core model
-- ---------------------------------------------------------------------------

structure ExecModel where
  Raw     : Type
  Class   : Type
  Rep     : Type
  Residue : Type
  Outcome : Type
  q         : Raw → Class
  evalRaw   : Raw → Outcome
  evalClass : Class → Outcome
  admissible : Class → Bool
  rho        : Class → Option Residue
  sigma      : Class → Option Rep

-- ---------------------------------------------------------------------------
-- Auxiliary predicate
-- ---------------------------------------------------------------------------

/-- A class is *active* if at least one raw event maps to it. -/
def activeClass (M : ExecModel) (c : M.Class) : Prop :=
  ∃ r : M.Raw, M.q r = c

-- ---------------------------------------------------------------------------
-- Tier 1: Execution structure axioms
-- (answer: "how to execute legally and non-redundantly")
-- ---------------------------------------------------------------------------

/-- R1 distinguish: raw execution factors through the quotient class.
    Raw identity cannot influence outcome; outcome is determined by class. -/
def quotientFactorization (M : ExecModel) : Prop :=
  ∀ r : M.Raw, M.evalRaw r = M.evalClass (M.q r)

/-- R2 constrain: if a class has a representative, it is admissible. -/
def admissibilitySound (M : ExecModel) : Prop :=
  ∀ (c : M.Class) (rep : M.Rep), M.sigma c = some rep → M.admissible c = true

/-- Φ5 totality: every active non-admissible class has a residue. -/
def residueTotality (M : ExecModel) : Prop :=
  ∀ c : M.Class, activeClass M c → M.admissible c = false → M.rho c ≠ none

/-- Φ2b precision: every active admissible class has a representative.
    Says "at least one exists"; does NOT say "at most one".
    The at-most-one condition is `AtMostOneAdmit` (Tier 2, orthogonal). -/
def representativePrecision (M : ExecModel) : Prop :=
  ∀ c : M.Class, activeClass M c → M.admissible c = true → M.sigma c ≠ none

-- ---------------------------------------------------------------------------
-- Tier 1 bundle: MST-NF execution profile
-- ---------------------------------------------------------------------------

/-- The four Tier 1 execution structure axioms bundled.
    Satisfying `hasMSTNFProfile` guarantees outcome uniformity,
    role completeness, and no silent failure.
    It does NOT guarantee admission uniqueness (see `AtMostOneAdmit`). -/
def hasMSTNFProfile (M : ExecModel) : Prop :=
  quotientFactorization M ∧
  admissibilitySound M ∧
  residueTotality M ∧
  representativePrecision M

-- ---------------------------------------------------------------------------
-- Core theorem: R1 — raw identity does not influence outcome
-- ---------------------------------------------------------------------------

/-- If raw execution factors through the class (quotientFactorization),
    then two raw events in the same class produce the same outcome.
    This is the key R1 content: outcome cannot depend on raw identity. -/
theorem sameClass_sameOutcome
    (M : ExecModel)
    (h : quotientFactorization M)
    {r1 r2 : M.Raw}
    (hq : M.q r1 = M.q r2) :
    M.evalRaw r1 = M.evalRaw r2 := by
  rw [h r1, h r2, hq]

-- ---------------------------------------------------------------------------
-- Profile bundling theorem
-- ---------------------------------------------------------------------------

theorem execModel_with_all_roles_has_mstnf_profile
    (M : ExecModel)
    (hQF : quotientFactorization M)
    (hAS : admissibilitySound M)
    (hRT : residueTotality M)
    (hRP : representativePrecision M) :
    hasMSTNFProfile M :=
  ⟨hQF, hAS, hRT, hRP⟩

-- ---------------------------------------------------------------------------
-- Tier 2: The fifth axiom — AtMostOneAdmit
-- (answer: "can two conflicting decisions both be admitted?")
-- ---------------------------------------------------------------------------

/-- **AtMostOneAdmit** — the fifth MST-NF axiom.
    For any admissible class, at most one raw event maps to it.
    Equivalently: q is injective on the preimage of every admissible class.

    This is the structural condition corresponding to election safety:
    if the q-class represents a decision slot (e.g., a term in Raft),
    then at most one candidate can be admitted per slot.

    ## Orthogonality to Tier 1

    `AtMostOneAdmit` is independent of all four Tier 1 axioms:

    * `representativePrecision` (∃ one) does NOT imply `AtMostOneAdmit`
      (∀ exactly one). Proof: `twoEltCollapse` in `MSTNFSafetyAxiomsMWE`.
    * `AtMostOneAdmit` does NOT imply `representativePrecision`.
      Proof: `singletonNoSigma` in `MSTNFSafetyAxiomsMWE`.

    ## Why this is the fifth axiom, not part of Tier 1

    `hasMSTNFProfile` answers "how to execute legally." `AtMostOneAdmit`
    answers "what the execution model prevents." These are different
    questions. A model can be well-formed (Tier 1) while permitting two
    conflicting admissions (¬ Tier 2), and vice versa. See `witnessModel`
    below: it satisfies all four Tier 1 axioms but violates `AtMostOneAdmit`
    because `primary` and `duplicate` both map to `canonical`. -/
def AtMostOneAdmit (M : ExecModel) : Prop :=
  ∀ (c : M.Class) (r1 r2 : M.Raw),
    M.q r1 = c → M.q r2 = c →
    M.admissible c = true →
    r1 = r2

-- ---------------------------------------------------------------------------
-- Tier 1 + Tier 2 bundle: full MST-NF safety profile
-- ---------------------------------------------------------------------------

/-- The full MST-NF profile bundling both tiers.
    A model satisfying `hasMSTNFSafetyProfile` guarantees:
    - Outcome uniformity (Tier 1)
    - Role completeness (Tier 1)
    - No silent failure (Tier 1)
    - Admission uniqueness (Tier 2: at most one raw per admissible class)

    This is the complete structural precondition for deriving both
    execution correctness and election-safety-type guarantees. -/
def hasMSTNFSafetyProfile (M : ExecModel) : Prop :=
  hasMSTNFProfile M ∧ AtMostOneAdmit M

-- ---------------------------------------------------------------------------
-- The gap theorem: Tier 1 does not imply Tier 2 (stated below, after witness)
-- ---------------------------------------------------------------------------

-- The witness `witnessModel` is constructed in §IX below; the gap theorem
-- `execModel_safety_requires_fifth_axiom` follows immediately after the
-- witness definitions.

-- ---------------------------------------------------------------------------
-- P1-B: Semantics must factor through the kernel quotient (constructive),
--        plus the classical bridge to the active image
-- ---------------------------------------------------------------------------

/-- The active image of q: classes that are actually reached by some raw input. -/
def ActiveClass {X Q : Type} (q : X → Q) : Type :=
  { c : Q // ∃ x : X, q x = c }

/-- The canonical map from X into the active image. -/
def qActive {X Q : Type} (q : X → Q) (x : X) : ActiveClass q :=
  ⟨q x, x, rfl⟩

/-- The active class carrier is definitionally the image of q.  This theorem is
    deliberately small: its purpose is to name the exact-image reading used by
    the paper-level "quotient before execution" argument. -/
theorem activeClass_is_image {X Q : Type} (q : X → Q) :
    ActiveClass q = { c : Q // ∃ x : X, q x = c } := rfl

/-- The kernel quotient of `q`: raw inputs identified when `q` maps them to the
    same class.  This is the constructive carrier of "raw events modulo
    structural indistinguishability"; it is an `abbrev` so that `Quot` API
    (`Quot.lift`, `Quot.inductionOn`, `Quot.sound`) applies directly. -/
abbrev KernelQuot {X Q : Type} (q : X → Q) : Type :=
  Quot (fun (x y : X) => q x = q y)

/-- The canonical map from X into the kernel quotient. -/
def qKernel {X Q : Type} (q : X → Q) (x : X) : KernelQuot q :=
  Quot.mk _ x

/-- The canonical map from the kernel quotient to the active image.
    Constructive: it only forgets the chosen representative embodied in a
    quotient point, never chooses one. -/
def kernelQuotToActiveClass {X Q : Type} (q : X → Q) :
    KernelQuot q → ActiveClass q :=
  Quot.lift
    (fun x => qActive q x)
    (by
      intro x y hxy
      apply Subtype.ext
      exact hxy)

/-- The canonical map is bijective.  Stated as a `Prop` this is constructive:
    surjectivity is an `∃` discharged inside `Prop` (where eliminating the
    `Prop`-valued witness `c.property` is allowed), and injectivity follows
    from `Quot.sound`.  Only turning this fact into an inverse *function*
    `ActiveClass q → KernelQuot q` needs `Classical.choice`; see
    `rawKernelQuotientEquivActiveClass_classical`. -/
theorem kernelQuotToActiveClass_bijective {X Q : Type} (q : X → Q) :
    (∀ z1 z2 : KernelQuot q,
      kernelQuotToActiveClass q z1 = kernelQuotToActiveClass q z2 → z1 = z2) ∧
    (∀ c : ActiveClass q, ∃ z : KernelQuot q, kernelQuotToActiveClass q z = c) := by
  constructor
  · intro z1 z2
    refine Quot.inductionOn z1 ?_
    refine Quot.inductionOn z2 ?_
    intro x y hxy
    apply Quot.sound
    exact congrArg Subtype.val hxy
  · intro c
    refine Exists.elim c.property ?_
    intro x hx
    exact ⟨Quot.mk _ x, Subtype.ext hx⟩

/-- A tiny local equivalence record, used to avoid importing any library just
    to name the set-level exact image bijection. -/
structure ExactEquiv (A B : Type) where
  toFun : A → B
  invFun : B → A
  left_inv : ∀ a : A, invFun (toFun a) = a
  right_inv : ∀ b : B, toFun (invFun b) = b

/-- First-isomorphism-style exactness for arbitrary functions — CLASSICAL form.

    Let two raw inputs be equivalent when q maps them to the same class.  The
    quotient of raw inputs by that kernel relation is equivalent to the active
    image of q.  This is the set-level image-factorization statement behind the
    MST-NF slogan "raw events modulo structural indistinguishability are exactly
    active quotient classes".

    **This declaration uses `Classical.choice`**: the inverse direction
    `ActiveClass q → KernelQuot q` must pick a representative `x` out of the
    `Prop`-level `∃ x, q x = c`, which CIC cannot do without an axiom.  The
    forward map `kernelQuotToActiveClass` and the *fact* of bijectivity
    (`kernelQuotToActiveClass_bijective`) are constructive; only the inverse
    *function* is classical.

    No theorem in this development depends on this equivalence: the
    factorization theorems are stated directly over `KernelQuot`, and the
    image-subtype form of P1-B is recoverable by composing with it.

    No group or algebraic operation is assumed here.  This is the quotient/image
    exactness layer, not a group first-isomorphism theorem. -/
noncomputable def rawKernelQuotientEquivActiveClass_classical {X Q : Type}
    (q : X → Q) :
    ExactEquiv (KernelQuot q) (ActiveClass q) where
  toFun := kernelQuotToActiveClass q
  invFun := fun c => qKernel q (Classical.choose c.property)
  left_inv := by
    intro z
    refine Quot.inductionOn z ?_
    intro x
    apply Quot.sound
    exact Classical.choose_spec (qActive q x).property
  right_inv := by
    intro c
    apply Subtype.ext
    exact Classical.choose_spec c.property

/-- P1-B: Any semantic interpretation that respects the MST quotient structure
    must factor uniquely through the kernel quotient.

    This is the universal property of the quotient: it is the mathematical
    statement of "semantics is defined by structure" — no admissible semantic
    interpretation can bypass the quotient map q.

    The statement is constructive (no `Classical.choice`): `m_bar` is
    `Quot.lift m h` itself, and uniqueness holds on every point of the kernel
    quotient by `Quot.inductionOn`.  The previously shipped form quantified
    over the subtype `ActiveClass q`; building `m_bar` there required choosing
    representatives, so it is now recovered only through the explicitly
    classical `rawKernelQuotientEquivActiveClass_classical`.  On the kernel
    quotient uniqueness is total rather than restricted to the image, because
    every quotient point is by definition hit by `qKernel`. -/
theorem semantics_factor_through_kernel_quotient
    {X Q D : Type}
    (q : X → Q)
    (m : X → D)
    (h : ∀ x y : X, q x = q y → m x = m y) :
    ∃ m_bar : KernelQuot q → D,
      (∀ x : X, m x = m_bar (qKernel q x)) ∧
      ∀ m_bar' : KernelQuot q → D,
        (∀ x : X, m x = m_bar' (qKernel q x)) →
        ∀ c : KernelQuot q, m_bar c = m_bar' c := by
  refine ⟨Quot.lift m h, ?_, ?_⟩
  · intro x
    rfl
  · intro m_bar' hm_bar' c
    refine Quot.inductionOn c ?_
    intro x
    exact hm_bar' x

/-- Corollary: on the ExecModel, any outcome function that respects quotientFactorization
    factors uniquely through the kernel quotient.
    This connects P1-B to the ExecModel vocabulary, constructively. -/
theorem execModel_semantics_factor_through_kernel_quotient
    (M : ExecModel)
    (hQF : quotientFactorization M) :
    ∃ m_bar : KernelQuot M.q → M.Outcome,
      (∀ r : M.Raw, M.evalRaw r = m_bar (qKernel M.q r)) ∧
      ∀ m_bar' : KernelQuot M.q → M.Outcome,
        (∀ r : M.Raw, M.evalRaw r = m_bar' (qKernel M.q r)) →
        ∀ c : KernelQuot M.q, m_bar c = m_bar' c := by
  apply semantics_factor_through_kernel_quotient
  intro r1 r2 hq
  exact sameClass_sameOutcome M hQF hq

-- ---------------------------------------------------------------------------
-- Concrete witness: a small model satisfying all four Tier 1 properties
-- but NOT AtMostOneAdmit — witnesses the fifth-axiom gap
-- ---------------------------------------------------------------------------

inductive RawEvent   where | primary | duplicate | unsafeEvt  deriving DecidableEq
inductive EventClass where | canonical | rejected           deriving DecidableEq
inductive Rep        where | rep0                           deriving DecidableEq
inductive Residue    where | unsafeResidue                  deriving DecidableEq
inductive Outcome    where | committed | blocked            deriving DecidableEq

/-- The canonical witness model. It satisfies all four Tier 1 axioms
    (`hasMSTNFProfile`) but violates `AtMostOneAdmit`: both `primary`
    and `duplicate` map to `canonical`, which is admissible, yet they
    are distinct raw events. This makes it the concrete witness of
    `execModel_safety_requires_fifth_axiom`. -/
def witnessModel : ExecModel where
  Raw     := RawEvent
  Class   := EventClass
  Rep     := Rep
  Residue := Residue
  Outcome := Outcome
  q := fun r => match r with
    | .primary   => .canonical
    | .duplicate => .canonical
    | .unsafeEvt => .rejected
  evalRaw := fun r => match r with
    | .primary   => .committed
    | .duplicate => .committed
    | .unsafeEvt => .blocked
  evalClass := fun c => match c with
    | .canonical => .committed
    | .rejected  => .blocked
  admissible := fun c => match c with
    | .canonical => true
    | .rejected  => false
  rho := fun c => match c with
    | .canonical => none
    | .rejected  => some .unsafeResidue
  sigma := fun c => match c with
    | .canonical => some .rep0
    | .rejected  => none

theorem witnessModel_quotientFactorization :
    quotientFactorization witnessModel := by
  intro r; cases r <;> rfl

theorem witnessModel_admissibilitySound :
    admissibilitySound witnessModel := by
  intro c rep h
  cases c <;> cases rep <;> simp [witnessModel] at h ⊢

theorem witnessModel_residueTotality :
    residueTotality witnessModel := by
  intro c ⟨r, hr⟩ hadm
  cases c with
  | canonical => simp [witnessModel] at hadm
  | rejected  => simp [witnessModel]

theorem witnessModel_representativePrecision :
    representativePrecision witnessModel := by
  intro c ⟨r, hr⟩ hadm
  cases c with
  | canonical => simp [witnessModel]
  | rejected  => simp [witnessModel] at hadm

theorem witnessModel_has_mstnf_profile :
    hasMSTNFProfile witnessModel :=
  execModel_with_all_roles_has_mstnf_profile witnessModel
    witnessModel_quotientFactorization
    witnessModel_admissibilitySound
    witnessModel_residueTotality
    witnessModel_representativePrecision

/-- The witness model violates `AtMostOneAdmit`: `primary` and `duplicate`
    are two distinct raw events that both q-map to `canonical` (admissible).
    This is the concrete proof of the fifth-axiom gap. -/
theorem witnessModel_not_atMostOneAdmit :
    ¬ AtMostOneAdmit witnessModel := by
  intro h
  -- h: ∀ c r1 r2, q r1 = c → q r2 = c → admissible c = true → r1 = r2
  -- Apply to c = canonical, r1 = primary, r2 = duplicate
  have := h EventClass.canonical RawEvent.primary RawEvent.duplicate rfl rfl rfl
  -- Lean derives primary = duplicate, which is false by DecidableEq
  exact RawEvent.noConfusion this

-- ---------------------------------------------------------------------------
-- The gap theorem (deferred from §IV, now applicable after witnessModel)
-- ---------------------------------------------------------------------------

/-- **The fifth-axiom gap**: `hasMSTNFProfile` does not imply
    `AtMostOneAdmit`. This is the formal statement of the gap
    discovered in the MST-NF axiom system.

    `witnessModel` (defined above) satisfies all four Tier 1 axioms but
    violates `AtMostOneAdmit`: `primary` and `duplicate` are distinct
    raw events that both map to `canonical` (an admissible class).

    Consequence: to derive election safety from MST-NF, one must
    explicitly verify `AtMostOneAdmit` for the concrete execution
    model. It is not a free consequence of well-formedness. -/
theorem execModel_safety_requires_fifth_axiom :
    ∃ M : ExecModel, hasMSTNFProfile M ∧ ¬ AtMostOneAdmit M :=
  ⟨witnessModel,
    witnessModel_has_mstnf_profile,
    witnessModel_not_atMostOneAdmit⟩

end MSTNecessityExecModelMWE
