import rcic.RcicAnnLR3PairedArms
import rcic.RcicAnnLR3UnitTranslate
import rcic.RcicAnnLR3NeutralControls

/-!
# Paired literal-expansion arms (`Ty_lit`, `Conv_lit`)

The evaluator's `natExpand` expansion law in paired form, and the two
literal arm contracts against it. The `ApproxI.lit` clause defines the
literal's approximation *by* the erased expansion, so the actual
`UnitModel` denotation of `.lit t` is literally equal (as a `Value`, via
`propext`/`funext`) to the denotation of `natExpand t`; `translate`
erases `natExpandA` to `natExpand`, and `approxI_natExpand_env`
discharges the closed expansion's environment independence needed when
the attached `image` interprets the expansion's outermost constant
specially (`NeutralControls.model` at `t = 0`).

The named premise `LitImageExpansion M` is the consumer-side shape of
that law: `M.image` must agree on a literal and its expansion at *each*
world. An arbitrary `AnnSemantics.image` does not guarantee it — the
expansion typing IH only covers the expansion endpoints — so the arm
suppliers are stated conditionally on it, exactly like
`ty_conv_supplied`'s `UniverseTransport`. The premise IS supplied for
the actual neutral-controls model (`model_litImageExpansion`); for any
other `M` it remains the caller's explicit obligation. The conditional
suppliers keep every source premise and the child-IH position verbatim.
`closure_claim = 0`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Rcic.Declarative.Ann.LR3.PairedLit

open Rcic.Declarative
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open Rcic.Declarative.Ann.LR3
open UnitModel TypedPER TypedStatements PairedStatements

/-! ## §1 the expansion law for the actual interpretation -/

/-- Translation erases the annotated literal expansion to the evaluator's
own `natExpand`. -/
theorem translate_natExpandA (ν : Valuation) : (t : Nat) →
    translate ν (natExpandA t) = natExpand t
  | 0 => rfl
  | t + 1 => congrArg litSucc (translate_natExpandA ν t)

/-- The `ApproxI.lit` clause as an invariance: a literal approximates
exactly what its erased expansion does. -/
theorem approxI_lit_expand_iff (ρ : EnvI) (t : Nat) (c : CptI) :
    ApproxI ρ (.lit t) c ↔ ApproxI ρ (natExpand t) c := by
  constructor
  · intro h
    rcases approxI_lit_inv h with h0 | h'
    · subst h0; exact .bot _ _
    · exact h'
  · intro h; exact .lit h

/-- Pointwise equality of the two denotations, by `propext`/`funext`. -/
theorem denI_lit_expand (ρ : EnvI) (t : Nat) :
    denI ρ (.lit t) = denI ρ (natExpand t) :=
  funext fun c => propext (approxI_lit_expand_iff ρ t c)

/-- A literal and its annotated expansion have the same denotation in
every environment — the unary form of the expansion law. -/
theorem denote_lit_expand (ν : Valuation) (ρ : EnvI) (t : Nat) :
    UnitModel.denote ν ρ (.lit t) = UnitModel.denote ν ρ (natExpandA t) := by
  show denI ρ (.lit t) = denI ρ (translate ν (natExpandA t))
  rw [translate_natExpandA]
  exact denI_lit_expand ρ t


/-! ## §2 the named premise and its paired transport laws -/

/-- Named premise: the attached semantics' image expands a literal to its
source expansion at each world. This is the consumer-side shape of the
evaluator's `natExpand` law — it is NOT discharged by the arm contracts
(the expansion IH covers only the expansion endpoints), and an arbitrary
`AnnSemantics.image` need not satisfy it. Supplied for the actual
neutral-controls model by `model_litImageExpansion`; for any other `M`
it remains the caller's explicit obligation. -/
def LitImageExpansion (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (t : Nat),
    M.image ν Γ ρ (.lit t) = M.image ν Γ ρ (natExpandA t)

/-- Paired form, both endpoints: the element relation assigned to the
type image transports the expansion-image relatedness to the literal
images. This is the "member support" the typing arm consumes. -/
theorem paired_lit_expand_both {M : AnnSemantics} (L : LitImageExpansion M)
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI} {t : Nat} {R : Relation}
    (h : R (M.image ν Γ ρ (natExpandA t)) (M.image μ Γ σ (natExpandA t))) :
    R (M.image ν Γ ρ (.lit t)) (M.image μ Γ σ (.lit t)) := by
  rw [L ν Γ ρ t, L μ Γ σ t]; exact h

/-- Paired form, left endpoint: used by the conversion arm, whose right
endpoint is already the expansion. -/
theorem paired_lit_expand_left {M : AnnSemantics} (L : LitImageExpansion M)
    {ν μ : Valuation} {Γ : LCtxA} {ρ σ : EnvI} {t : Nat} {R : Relation}
    (h : R (M.image ν Γ ρ (natExpandA t)) (M.image μ Γ σ (natExpandA t))) :
    R (M.image ν Γ ρ (.lit t)) (M.image μ Γ σ (natExpandA t)) := by
  rw [L ν Γ ρ t]; exact h

/-- Member form: literal-image membership follows from expansion-image
membership in a single world. -/
theorem paired_lit_expand_member {M : AnnSemantics} (L : LitImageExpansion M)
    {ν : Valuation} {Γ : LCtxA} {ρ : EnvI} {t : Nat} {R : Relation}
    (h : Member R (M.image ν Γ ρ (natExpandA t))) :
    Member R (M.image ν Γ ρ (.lit t)) := by
  rw [L ν Γ ρ t]; exact h

/-! ## §3 the two arm suppliers -/

/-- The `Ty_lit` arm, conditional on `LitImageExpansion` (named premise;
see its docstring for why it is needed: the conclusion relates the
*literal* images in both worlds while the child IH relates only the
expansion images). Every source premise and the child-IH position are
kept verbatim — `hexp` is retained as the contract requires. -/
theorem ty_lit_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) (L : LitImageExpansion M) :
    PairedArms.Ty_lit M E I n := by
  intro Γ t T _hexp ih_hexp hΓ ν μ ρ σ _hν hρ
  obtain ⟨k, R, S, hc, hr⟩ := ih_hexp hΓ ν μ ρ σ _hν hρ
  exact ⟨k, R, S, hc, paired_lit_expand_both L hr⟩

/-- The `Conv_lit` arm, conditional on `LitImageExpansion` (named
premise). The conclusion relates the left literal image to the right
expansion image; only the left world needs the expansion law. Every
source premise and the child-IH position are kept verbatim. -/
theorem conv_lit_supplied (M : AnnSemantics) (E : ResolvedEnvA)
    (I : IotaIfaceA) (n : Nat) (L : LitImageExpansion M) :
    PairedArms.Conv_lit M E I n := by
  intro Γ t T _hexp ih_hexp hΓ ν μ ρ σ _hν hρ
  obtain ⟨k, R, S, hc, hr⟩ := ih_hexp hΓ ν μ ρ σ _hν hρ
  exact ⟨k, R, S, hc, paired_lit_expand_left L hr⟩

/-! ## §4 member support for the actual model -/

/-- The actual `NeutralControls.model` interprets the expansion's
outermost constant as a closed neutral atom (`t = 0`) and the successor
application through the denotation (`t + 1`); both land on
`denI ρ (natExpand t)` — the former by `approxI_natExpand_env`. -/
theorem model_image_natExpandA (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (t : Nat) :
    NeutralControls.model.image ν Γ ρ (natExpandA t) = denI ρ (natExpand t) := by
  cases t with
  | zero =>
      show NeutralPER.neutralAtom 1 = denI ρ (.const 1 [])
      funext c
      apply propext
      constructor
      · exact fun h => approxI_natExpand_env EnvI.bot ρ 0 h
      · exact fun h => approxI_natExpand_env ρ EnvI.bot 0 h
  | succ t =>
      show UnitModel.denote ν ρ (.app (.const 2 []) (natExpandA t)) = denI ρ (natExpand (t + 1))
      show denI ρ (.app (constantTerm 2) (translate ν (natExpandA t))) = _
      rw [translate_natExpandA]
      rfl

/-- The actual model supplies the named premise: its literal image and
expansion image are the same value in every world. -/
theorem model_litImageExpansion : LitImageExpansion NeutralControls.model := by
  intro ν Γ ρ t
  show UnitModel.denote ν ρ (.lit t) = _
  rw [model_image_natExpandA]
  show denI ρ (.lit t) = denI ρ (natExpand t)
  exact denI_lit_expand ρ t

/-- The concrete `Ty_lit` supplier for the actual model — the named
premise is discharged by `model_litImageExpansion`. -/
theorem ty_lit_supplied_model (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Ty_lit NeutralControls.model E I n :=
  ty_lit_supplied _ _ _ _ model_litImageExpansion

/-- The concrete `Conv_lit` supplier for the actual model. -/
theorem conv_lit_supplied_model (E : ResolvedEnvA) (I : IotaIfaceA) (n : Nat) :
    PairedArms.Conv_lit NeutralControls.model E I n :=
  conv_lit_supplied _ _ _ _ model_litImageExpansion

end Rcic.Declarative.Ann.LR3.PairedLit
