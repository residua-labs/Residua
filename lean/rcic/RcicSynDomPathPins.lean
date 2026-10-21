import rcic.RcicSynDomPath

/-!
# T12 pins — the S7 §4 `trans (symm b) b` control (ChatGPT S7, #7330)

Spec: `research/rcic/sortrow/S7_ORIGINAL_DOMAIN_KIND_TRACE.md` §4.
`closure_claim = 0`.

§4's control: `b : R ≡ P : s_U` is a beta conversion at `sort (imax 1 1)` with
`R := (λ s₁. P) s₀`, `P := Π s₀. s₀`; `C := trans (symm b) b : P ≡ P : s_U`
folds through the literal `app` middle `R`. The §3 reader must keep the
`nonPiMiddle` demand — both ends are Π while the middle is a redex, so the wrong
decomposition "every child is Π→Π" is refused. The weights pin the spec's
numbers: `pP = 3`, `pR = 9`, `wt b = 18`, `wt (symm b) = 31`, `wt C = 56`.
The reflexive conclusion of the folded path — `P`'s domain `s₀` converts to
itself — is `dpDomSame` / `dpDomSame_trace`, a K1-class fact.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-- `s₀ := sort 0`. -/
abbrev dpS0 : Expr Nat := .sort .zero
/-- `s₁ := sort 1`. -/
abbrev dpS1 : Expr Nat := .sort (.succ .zero)
/-- `P := Π s₀. s₀`. -/
abbrev dpP : Expr Nat := .pi dpS0 dpS0
/-- `s_U := sort (imax 1 1)`. -/
abbrev dpU : Level := .imax (.succ .zero) (.succ .zero)
/-- `R := (λ s₁. P) s₀` — the literal `app` middle, a beta redex, never a `pi`. -/
abbrev dpR : Expr Nat := .app (.lam dpS1 dpP) dpS0

/-- `s₀ : s₁` at any `Γ`. -/
def dpTyS0 {Γ : LCtx} : TyP emptyEnv 0 Γ dpS0 dpS1 :=
  .sort _ _ _ .zero (.succ .zero) (eqN_refl _)

/-- `s₁ : s₂` at any `Γ`. -/
def dpTyS1 {Γ : LCtx} : TyP emptyEnv 0 Γ dpS1 (.sort (.succ (.succ .zero))) :=
  .sort _ _ _ (.succ .zero) (.succ (.succ .zero)) (eqN_refl _)

/-- `pP : TyP Γ P (sort (imax 1 1))` — the `wt = 3` natural typing of `P`. -/
def dpTyPIn {Γ : LCtx} : TyP emptyEnv 0 Γ dpP (.sort dpU) :=
  .pi _ _ _ _ _ _ _ dpTyS0 dpTyS0

/-- `λ s₁. P : Π s₁. s_U`. -/
def dpTyLam : TyP emptyEnv 0 [] (.lam dpS1 dpP) (.pi dpS1 (.sort dpU)) :=
  .lam _ _ _ _ _ _ _ _ dpTyS1 dpTyPIn (.sort _ _ _ dpU (.succ dpU) (eqN_refl _))

/-- `pR : TyP [] R s_U` — `wt = 9`. -/
def dpTyR : TyP emptyEnv 0 [] dpR (.sort dpU) :=
  .app _ _ _ _ _ _ _ _ dpTyLam dpTyS0 (.sort _ _ _ dpU (.succ dpU) (eqN_refl _))

/-- `b : R ≡ P : s_U` — the original beta node, `wt = 18`. -/
def dpB : CvP emptyEnv 0 [] dpR dpP (.sort dpU) :=
  .beta _ _ _ _ _ _ _ _ dpTyS1 dpTyPIn dpTyS0 dpTyR dpTyPIn

/-- `symm b : P ≡ R : s_U` — `wt = 31`. -/
def dpSymmB : CvP emptyEnv 0 [] dpP dpR (.sort dpU) :=
  .symm _ _ _ _ _ _ dpB dpTyPIn dpTyR

/-- `C := trans (symm b) b : P ≡ P : s_U` — `wt = 56`, folding through the
    literal `app` middle `R`. -/
def dpC : CvP emptyEnv 0 [] dpP dpP (.sort dpU) :=
  .trans _ _ _ _ _ _ _ dpSymmB dpB dpTyPIn dpTyPIn

theorem dpTyP_wt (Aw : Nat → Nat) : (dpTyPIn (Γ := [])).wt Aw = 3 := rfl
theorem dpTyR_wt (Aw : Nat → Nat) : dpTyR.wt Aw = 9 := rfl
theorem dpB_wt (Aw : Nat → Nat) : dpB.wt Aw = 18 := rfl
theorem dpSymmB_wt (Aw : Nat → Nat) : dpSymmB.wt Aw = 31 := rfl
theorem dpC_wt (Aw : Nat → Nat) : dpC.wt Aw = 56 := rfl

/-- §4 control: the literal `app` middle is never a `pi`. -/
theorem dpR_not_pi : ∀ A B : Expr Nat, dpR ≠ .pi A B := fun _ _ h =>
  Expr.noConfusion h

/-- §4 control: `domRead` of `trans (symm b) b` keeps the demand — the `app`
    middle makes it a `nonPiMiddle` obligation with the two child reads recorded
    (`symm`'s own obligation wrapped, `b`'s `arm` kept). Never a forced Π→Π
    read; never "the reader returned none, so the demand does not exist". The
    reader is entered at the actual occurrence `.root` of `dpC` inside its own
    forest — every edge it emits is a `CvPOcc` step from there. -/
theorem domRead_dpC :
    ∃ hnot, domRead dpC .root =
      .obligation (.nonPiMiddle hnot
        (.obligation (.symm (.arm dpB))) (.obligation (.arm dpB))) :=
  ⟨_, rfl⟩

/-- A literal `CvP.pi` at reflexive children — for the §3 positive arm pin. -/
def dpCvPiRefl {Γ : LCtx} : CvP emptyEnv 0 Γ dpS0 dpS0 (.sort (.succ .zero)) :=
  .refl _ _ _ _ _ dpTyS0 dpTyS0 dpTyS0

/-- `CvP.pi` over the reflexive children: `P ≡ P : s_U`. -/
def dpCvPi : CvP emptyEnv 0 [] dpP dpP (.sort dpU) :=
  .pi _ _ _ _ _ _ _ _ _ dpCvPiRefl dpCvPiRefl dpTyPIn dpTyPIn

/-- §3's cheapest positive arm: a literal `CvP.pi` reads as `DomPath.edge` on the
    original `hA` — the original field handed over directly at the `.piHA`
    occurrence step, never rebuilt. -/
theorem domRead_dpCvPi :
    domRead dpCvPi .root =
      .path (.edge dpCvPiRefl (.step .root (.head _))) rfl rfl := rfl

/-- `symm` of the `CvP.pi` — §3's `symm` arm: the child's `path` is viewed
    through `DomPath.reverse`, no larger symm judgment is rebuilt. -/
def dpSymmPi : CvP emptyEnv 0 [] dpP dpP (.sort dpU) :=
  .symm _ _ _ _ _ _ dpCvPi dpTyPIn dpTyPIn

theorem domRead_dpSymmPi :
    domRead dpSymmPi .root =
      .path (.reverse (.edge dpCvPiRefl (.step (.step .root (.head _)) (.head _))))
        rfl rfl := rfl

/-- P2 refusal control: a freshly built `CvP.symm` — not a field of the original
    `CvP.pi` node — is rejected: it is no `CvPChild` of `dpCvPi`. -/
def dpGenSymm : CvP emptyEnv 0 [] dpR dpP (.sort dpU) :=
  .symm _ _ _ _ _ _ dpSymmB dpTyR dpTyPIn

theorem edge_no_generated_symm_field :
    ¬ CvPChild (.mk dpCvPi) (.mk dpGenSymm) := fun h => by
  cases h <;> rename_i s' <;> cases s' <;> rename_i s'' <;> cases s''

/-- `dpCvPiRefl` at `Γ = []` — the `hA` field of `dpCvPi`. -/
def dpCvPiRefl0 : CvP emptyEnv 0 [] dpS0 dpS0 (.sort (.succ .zero)) :=
  dpCvPiRefl

/-- `dpCvPiRefl` at the `pi`-body context `assumption s₀ :: []` — the `hB`
    field of `dpCvPi`. -/
def dpCvPiReflA : CvP emptyEnv 0 [.assumption dpS0] dpS0 dpS0
    (.sort (.succ .zero)) := dpCvPiRefl

/-- The occurrence enumeration of `dpCvPi`'s forest: exactly the node itself
    and its two literal `CvP` fields (the `hA` domain conversion at `Γ`, the
    `hB` body conversion under `assumption s₀ :: Γ`). -/
theorem cvPOcc_dpCvPi {c : CvPAny}
    (h : CvPOcc (.mk dpCvPi) c) :
    c = .mk dpCvPi ∨ c = .mk dpCvPiRefl0 ∨ c = .mk dpCvPiReflA := by
  induction h with
  | root => exact .inl rfl
  | step _ s ih =>
      rcases ih with e | e | e
      · have s' := e ▸ s
        cases s' with
        | head => exact .inr (.inl rfl)
        | tail =>
            rename_i s''
            cases s'' with
            | head => exact .inr (.inr rfl)
            | tail => rename_i s'''; cases s'''
      · have s' := e ▸ s
        cases s'
      · have s' := e ▸ s
        cases s'

/-- P2 refusal control: the freshly built `CvP.symm` has no `CvPOcc` in
    `dpCvPi`'s forest — `DomPath.edge` cannot be instantiated with it. Every
    member of the forest has a different lhs than the generated node's `dpR`. -/
theorem edge_refuses_generated_symm :
    ¬ CvPOcc (.mk dpCvPi) (.mk dpGenSymm) := fun h => by
  rcases cvPOcc_dpCvPi h with e | e | e <;> cases e

/-- §4's folded-path domain conclusion: `P`'s domain `s₀` converts to itself —
    a `DomPath.same` on the actual domain typing (inside `dpCvPi`'s forest). -/
def dpDomSame :
    DomPath (.mk dpCvPi) emptyEnv 0 [] dpS0 dpS0 := .same dpTyS0

/-- Its `KindTrace`: two reflexive alignments against the actual domain typing. -/
theorem dpDomSame_trace {σ : Level → Level} :
    KindTrace σ dpDomSame dpTyS0 dpTyS0 :=
  .same (eqN_refl _) (eqN_refl _)

/-- §4's reflexive conclusion, as the composed bit equation at `dpS0`'s sort. -/
theorem dpDomSame_eqN {σ : Level → Level} :
    eqN (σ (.succ .zero)) (σ (.succ .zero)) :=
  kindTrace_sortCoh dpDomSame_trace

end Rcic.Syn

#print axioms Rcic.Syn.dpTyP_wt
#print axioms Rcic.Syn.dpTyR_wt
#print axioms Rcic.Syn.dpB_wt
#print axioms Rcic.Syn.dpSymmB_wt
#print axioms Rcic.Syn.dpC_wt
#print axioms Rcic.Syn.dpR_not_pi
#print axioms Rcic.Syn.domRead_dpC
#print axioms Rcic.Syn.domRead_dpCvPi
#print axioms Rcic.Syn.domRead_dpSymmPi
#print axioms Rcic.Syn.edge_no_generated_symm_field
#print axioms Rcic.Syn.cvPOcc_dpCvPi
#print axioms Rcic.Syn.edge_refuses_generated_symm
#print axioms Rcic.Syn.dpDomSame
#print axioms Rcic.Syn.dpDomSame_trace
#print axioms Rcic.Syn.dpDomSame_eqN
