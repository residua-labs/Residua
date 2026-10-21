import rcic.RcicNativePiModelLRTermD

/-!
# RcicNativePiModelTermDCases — the `irr` and `eta` cases of `FundamentalTermD`

Third revision, scoped to `irr` + `eta`: K / η-K at non-canonical proof majors
(`KIotaLinkD`, `EtaKChainD`) and the family fundamental lemma moved to the
desktop-Opus lane — this module keeps only the irr/η cases plus the shared
ι/λ machinery that lane consumes (`whRed_of_derivedIota`,
`lrTermD_of_whRed_diag`, `lrTermD_lam_congr`).

Built on devin-fcd's repaired relation `LRTermD` (`RcicNativePiModelLRTermD`,
#7646's `fbd1a63683`), which carries the proposition collapse inside the
relation — `LRTermD = IsPropTyI ∨ LRTermDCore` with `lrTermD_prop_total` — and
a real data-spine reading.

* `irrCaseD : IrrCaseD` : the `ConvT.irr` case.  `p ~ q : P` with `P : Sort 0`
  is related at every compact — `LRTermD` is total at propositions.  The only
  hypothesis beyond `ConvT.irr`'s own fields is `∀ l, P ≠ .sort l`, the
  syntactic side-condition `IsPropTyI` needs (a literal `.sort l` is never a
  proposition); `irrCaseD_witness` shows the premises inhabited at a Prop
  variable.

* `etaCaseD (hd : EtaDiagD E n) : EtaCaseD E n` : the `eta` case, discharged
  modulo the single honest premise `EtaDiagD` — `f` self-related at the
  η-expansion's own `lam` compacts, with the full typing and `ApproxI`
  membership kept.  `u = .bot` is `lrTermD_bot`; at `u = .lam g` the
  `lam` clause's demanded application `app (λx. f x) N ~ app f N'` is
  `lrTermD_expand` along the compiled computation `whRed_etaApp`
  (`instantiate0_etaBody` via `instantiate_lift_id` + `WhStep.beta`).
  `EtaDiagD` is what `FundamentalTermD`'s diagonal at `f` supplies once the
  step tables of `λx. f x` and `f` are identified (substitution adequacy);
  `etaDiagD_nil` compiles it at the empty table — the premise is inhabited,
  not vacuous.

* Shared machinery the K/η-K lane consumes: `lrTermD_lam_congr` (`LRTermDCore`
  congruent under λ at a Π index — the under-binder step), and the ι-route
  helpers `whRed_of_derivedIota` (`DerivedIota → WhRed`, canonical majors) and
  `lrTermD_of_whRed_diag` (a wh-reduction plus the right side's diagonal gives
  the relation).

`closure_claim = 0`.  No `sorry`, no new axiom.
-/

namespace Rcic.Declarative.NativeValleys.PiModelTermAudit

open Rcic.Declarative.NativeValleys.PiModelIdealAudit

variable {E : ResolvedEnv} {n : Nat}

/-! ### the η computation -/

/-- The η-expansion body `app (lift 0 1 f) (bvar 0)` instantiated at `N` computes to
    `app f N` — the β-reduct of the η-expanded application. -/
theorem instantiate0_etaBody {f N : Expr Nat} :
    instantiate0 N (.app (lift 0 1 f) (.bvar 0)) = .app f N :=
  congrArg (fun x => Expr.app x N) (instantiate_lift_id 0 N f)

/-- One weak-head step: `app (lam A (app (lift 0 1 f) (bvar 0))) N ↝ app f N`. -/
theorem whStep_etaApp (A f N : Expr Nat) :
    WhStep E (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) N) (.app f N) := by
  have h := @WhStep.beta E A (.app (lift 0 1 f) (.bvar 0)) N
  rw [instantiate0_etaBody] at h
  exact h

/-- The η-expanded application weak-head reduces to the plain application. -/
theorem whRed_etaApp (A f N : Expr Nat) :
    WhRed E (.app (.lam A (.app (lift 0 1 f) (.bvar 0))) N) (.app f N) :=
  .step (whStep_etaApp A f N) (.refl _)

/-! ### `irr` — proposition-level triviality, no premise -/

/-- The `irr` case of `FundamentalTermD`: `p ~ q : P` with `P : Sort 0`.  The
    last hypothesis is the syntactic side-condition `IsPropTyI` needs — a
    literal `.sort l` is never a proposition, so the premise holds of every
    genuine proposition term; `irrCaseD_witness` shows it inhabited. -/
def IrrCaseD (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {P p q : Expr Nat},
    HasTyT E n Γ P (.sort .zero) → HasTyT E n Γ p P → HasTyT E n Γ q P →
    (∀ l, P ≠ .sort l) →
    ∀ u, ApproxI EnvI.bot p u → LRTermD E n Γ p q P u

/-- `irr` holds by `LRTermD`'s own proposition collapse — no external premise. -/
theorem irrCaseD : IrrCaseD E n := by
  intro Γ P p q hP _ _ hns u _
  exact lrTermD_prop_total ⟨hP⟩ hns u

/-- Non-vacuity: the `irr` premises are inhabited — a proposition VARIABLE
    `X : Prop` (context `X : Sort 0 ⊢`) is a proposition index, and every pair
    of terms is related there at every compact. -/
theorem irrCaseD_witness (u : CptI) :
    LRTermD E n [.assumption (.sort .zero)] (.bvar 0) (.bvar 0) (.bvar 0) u :=
  lrTermD_prop_total ⟨.bvar [.assumption (.sort .zero)] 0 (.sort .zero) rfl⟩
    (fun _ h => nomatch h) u

/-! ### `eta` — expansion + the application, hypotheses kept -/

/-- The premise the `eta` case reduces to: `f` self-related at the
    η-expansion's own `lam` compact, with the `ApproxI`-membership hypothesis
    made explicit — for every `lam g` the η-expansion approximates, `f` is
    related to itself there.  `FundamentalTermD`'s diagonal at `f` supplies it
    once the step tables of `λx. f x` and `f` are identified (substitution
    adequacy); `etaDiagD_nil` compiles it at the empty table. -/
def EtaDiagD (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx} {f A B : Expr Nat} {w : Level},
    HasTyT E n Γ f (.pi A B) →
    Nonempty (CtxWfT E n (.assumption A :: Γ)) →
    Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort w)) →
    ∀ {g : List (List CptI × CptI)},
      ApproxI EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) (.lam g) →
      LRTermD E n Γ f f (.pi A B) (.lam g)

/-- The `eta` case of `FundamentalTermD`: `λx. f x ~ f : Π A B`, with the full
    typing presuppositions (`CtxWfT` of the extended context, the codomain
    typed at its sort, `f` typed at the Π) and `ApproxI` membership of the
    η-expansion kept. -/
def EtaCaseD (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {f A B : Expr Nat} {w : Level},
    HasTyT E n Γ f (.pi A B) →
    Nonempty (CtxWfT E n (.assumption A :: Γ)) →
    Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort w)) →
    ∀ u, ApproxI EnvI.bot (.lam A (.app (lift 0 1 f) (.bvar 0))) u →
      LRTermD E n Γ (.lam A (.app (lift 0 1 f) (.bvar 0))) f (.pi A B) u

/-- `eta` from `EtaDiagD`: `u = .bot` is trivial; at `u = .lam g` the `lam`
    clause's demanded application `app (λx. f x) N ~ app f N'` is
    `lrTermD_expand` along `whRed_etaApp` applied to `f`'s own application
    reading, which `EtaDiagD`'s `lam` clause supplies. -/
theorem etaCaseD (hd : EtaDiagD E n) : EtaCaseD E n := by
  intro Γ _ f A B w hf hΓ₁ hB u hu
  rcases approxI_lam_inv hu with h0 | ⟨g, rfl, hg⟩
  · rw [h0]; exact lrTermD_bot _ _ _ _
  · rcases hd hf hΓ₁ hB (.lam hg) with hP | hcore
    · exact Or.inl hP
    · refine Or.inr ?_
      rw [LRTermDCore.eq_def] at hcore ⊢
      obtain ⟨A₁, B₁, w', hA₁, hΓ₁', hB₁', happ⟩ := hcore
      exact ⟨A₁, B₁, w', hA₁, hΓ₁', hB₁', fun s hs N N' hN hN' hrel =>
        lrTermD_expand (whRed_etaApp A f N) (.refl _) s.2
          (happ s hs N N' hN hN' hrel)⟩

/-- Non-vacuity for `EtaDiagD`: at the empty step table the diagonal follows
    from the typing presuppositions alone — the `lam` clause quantifies over
    `s ∈ []` vacuously. -/
theorem etaDiagD_nil {Γ : LCtx} {f A B : Expr Nat} {w : Level}
    (hΓ₁ : Nonempty (CtxWfT E n (.assumption A :: Γ)))
    (hB : Nonempty (HasTyT E n (.assumption A :: Γ) B (.sort w))) :
    LRTermD E n Γ f f (.pi A B) (.lam []) := by
  refine Or.inr ?_
  rw [LRTermDCore.eq_def]
  exact ⟨A, B, w, .refl _, hΓ₁, hB, fun s hs => absurd hs (List.not_mem_nil _)⟩

/-! ### shared ι/λ machinery (consumed by the K/η-K lane) -/

/-- `LRTermDCore` is congruent under `lam` at a Π index: the `lam` clause's
    per-demand output reduces, after the β steps `app (lam P b) N ↝ b[N]` and
    `app (lam P b') N' ↝ b'[N']` (`lrTermD_expand`), to the body relation —
    `LRTermD`'s disjunction is exactly the clause's output shape.  The
    under-binder step the K/η-K lane's links consume. -/
theorem lrTermD_lam_congr {Γ : LCtx} {P b b' B : Expr Nat} {w : Level}
    {g : List (List CptI × CptI)}
    (hΓ₁ : Nonempty (CtxWfT E n (.assumption P :: Γ)))
    (hB : Nonempty (HasTyT E n (.assumption P :: Γ) B (.sort w)))
    (hbody : ∀ s ∈ g, ∀ N N' : Expr Nat, HasTyT E n Γ N P → HasTyT E n Γ N' P →
      (∀ u ∈ s.1, LRTermDCore E n Γ N N' P u) →
      LRTermD E n Γ (instantiate0 N b) (instantiate0 N' b') (instantiate0 N B) s.2) :
    LRTermDCore E n Γ (.lam P b) (.lam P b') (.pi P B) (.lam g) := by
  rw [LRTermDCore.eq_def]
  refine ⟨P, B, w, .refl _, hΓ₁, hB, fun s hs N N' hN hN' hrel => ?_⟩
  exact lrTermD_expand (.step (@WhStep.beta E P b N) (.refl _))
    (.step (@WhStep.beta E P b' N') (.refl _)) s.2
    (hbody s hs N N' hN hN' hrel)

/-- The ι premise is inhabited: every `DerivedIota` landing (the canonical-major
    case `ConvT.iota` covers) is a weak-head reduction.  The reduction half of
    the ι route the K/η-K lane consumes. -/
theorem whRed_of_derivedIota {lhs rhs : Expr Nat} (d : DerivedIota E lhs rhs) :
    WhRed E lhs rhs :=
  .step (.iota (derivedIotaU_ofDerivedIota d)) (.refl _)

/-- A weak-head reduction on the left plus the right side's diagonal gives the
    relation — `lrTermD_expand`.  The ι-route consumer at canonical majors. -/
theorem lrTermD_of_whRed_diag {Γ : LCtx} {lhs m B : Expr Nat} {u : CptI}
    (hred : WhRed E lhs m) (hdiag : LRTermD E n Γ m m B u) :
    LRTermD E n Γ lhs m B u :=
  lrTermD_expand hred (.refl _) u hdiag

#print axioms instantiate0_etaBody
#print axioms whStep_etaApp
#print axioms whRed_etaApp
#print axioms IrrCaseD
#print axioms irrCaseD
#print axioms irrCaseD_witness
#print axioms EtaDiagD
#print axioms EtaCaseD
#print axioms etaCaseD
#print axioms etaDiagD_nil
#print axioms lrTermD_lam_congr
#print axioms whRed_of_derivedIota
#print axioms lrTermD_of_whRed_diag

end Rcic.Declarative.NativeValleys.PiModelTermAudit
