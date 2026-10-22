import rcic.RcicAnnLR3PairedArms
import rcic.RcicAnnLR3UnitTranslate

/-!
# Paired lookup arms — `PairedArms.Ty_bvar`, `PairedArms.Conv_zetaLocal`

Variable and stored-let lookup for the paired model route, supplied
against the `RcicAnnLR3PairedArms` contracts.

## Evaluator laws for the actual interpretation

`UnitModel.denote`/`translate` is the actual image.  The two evaluator
laws this route needs are proved here for that interpretation:

* `denote_image_bvar` — `UnitModel.denote ν ρ (.bvar i) = fun c => c = .bot ∨ ρ i c`.
  Every `denI` value contains `.bot` (the `ApproxI.bot` constructor), so
  a variable's image is its environment entry **adjoined with `.bot`**,
  not the bare entry `ρ i`.
* `denote_image_lift` —
  `UnitModel.denote ν ρ (liftA 0 k e) = UnitModel.denote ν (EnvI.drop ρ k) e`:
  the `i+1`-lifted stored declaration is interpreted in the `i+1`-dropped
  tail environment (via `approxI_liftN_intro` / `approxI_liftN_elim`).

## Named premises — what the arms need of the model

`AnnSemantics.image` is a free field beyond `sort_image`, so neither arm
is derivable for an arbitrary `M`.  Each arm is supplied against its
contract under named premises:

* `ImageLiftLaw M` — image transports `liftA 0 k` into the `k`-dropped
  tail environment.  **Discharged** for any semantics whose image is the
  actual interpretation (`imageLiftLaw_of_denoteImage`).
* `ImageBvarRelL M` / `ImageBvarRelR M` — `.bvar i`'s image inherits the
  entry's relatedness on the left/right.  **This is the residual.**
  For the actual interpretation
  `denote_image_bvar` reduces these to closure of the code relation under
  `.bot`-adjunction of the stored entry
  (`bvarImageRelL_of_denoteImage`, `bvarImageRelR_of_denoteImage`) —
  a property of the relations `M` assigns, not of `AnnSemantics`.
  A relation on `denI`-built values satisfies it whenever its arguments
  are `.bot`-closed; `AnnSemantics` does not state it.

## Arm supplies (conditional consumers — measurements)

`paired_ty_bvar_of_laws` and `paired_conv_zetaLocal_of_laws` consume the
named premises and produce the exact contract types.  Every source
premise and the child-IH position are kept; `HasTyA`, the child IH,
`CtxWfA`, and `ValuationRel` are not consumed — `PairedRealises` already
carries the entry's code pair, relatedness, and stored-value agreements.

## Lookup extraction

`pairedRealises_entry_assumption` / `pairedRealises_entry_letBinding`
align `Γ.get? i` with the `i`-th `EnvI.cons` layer of a `PairedRealises`
derivation, exposing the entry's `CodePair` in the `i+1`-dropped tail
environments; `pairedRealises_lookupType` /
`pairedRealises_lookupValueType` package them at `lookupTypeA` /
`lookupValueA`.
-/

namespace Rcic.Declarative.Ann.LR3.PairedLookup

open Rcic.Declarative
open TypedStatements PairedStatements
open Rcic.Declarative.NativeValleys
open Rcic.Declarative.NativeValleys.PiModelIdealAudit
open UnitModel TypedPER

section ImageLaws

/-- Stored-type lift transport: `image` of the `k`-lifted stored
declaration equals `image` of the declaration in the `k`-dropped tail
environment.  `lookupTypeA`/`lookupValueA` return `liftA 0 (i+1) a`
while `PairedRealises` entries carry the unlifted `a` in the tail
environment, so both lookup arms consume this law.  Discharged for the
actual interpretation by `imageLiftLaw_of_denoteImage`; not derivable
from `AnnSemantics` alone. -/
def ImageLiftLaw (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (k : Nat) (e : ExprA),
    M.image ν Γ ρ (liftA 0 k e) = M.image ν (Γ.drop k) (EnvI.drop ρ k) e

/-- Left entry-relatedness of variable images: `.bvar i`'s image keeps
whatever relation its `i`-th environment entry has to any `W`.  For the
actual interpretation the image is `fun c => c = .bot ∨ ρ i c`, so this
law is `.bot`-adjunction closure of the relation on the left argument —
a property of the relations `M` assigns, not of `AnnSemantics`.  This is
a named residual premise of both lookup arms. -/
def ImageBvarRelL (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (i : Nat) (R : Relation)
    (x W : Value), ρ i = x → R x W → R (M.image ν Γ ρ (.bvar i)) W

/-- The mirror law on the right argument. -/
def ImageBvarRelR (M : AnnSemantics) : Prop :=
  ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (i : Nat) (R : Relation)
    (W y : Value), ρ i = y → R W y → R W (M.image ν Γ ρ (.bvar i))

/-- The actual interpretation of a variable is the environment entry
adjoined with `.bot` — every `denI` value contains `.bot` via
`ApproxI.bot`. -/
theorem denote_image_bvar (ν : Valuation) (ρ : EnvI) (i : Nat) :
    UnitModel.denote ν ρ (.bvar i) = fun c => c = .bot ∨ ρ i c := by
  funext c
  exact propext ⟨fun h => approxI_bvar_inv h,
    fun h => h.elim (fun e => e ▸ ApproxI.bot ρ _) ApproxI.bvar⟩

/-- The actual interpretation transports source lifts into dropped
environments. -/
theorem denote_image_lift (ν : Valuation) (ρ : EnvI) (k : Nat) (e : ExprA) :
    UnitModel.denote ν ρ (liftA 0 k e) = UnitModel.denote ν (EnvI.drop ρ k) e := by
  funext c
  show ApproxI ρ (translate ν (liftA 0 k e)) c =
    ApproxI (EnvI.drop ρ k) (translate ν e) c
  rw [translate_lift]
  exact propext ⟨fun h => approxI_liftN_elim ρ k h,
    fun h => approxI_liftN_intro ρ k h⟩

/-- `ImageLiftLaw` holds for any semantics whose image is the actual
`denote`/`translate` interpretation.  This is the evaluator-law
discharge for the actual model route. -/
theorem imageLiftLaw_of_denoteImage {M : AnnSemantics}
    (him : ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (e : ExprA),
      M.image ν Γ ρ e = UnitModel.denote ν ρ e) :
    ImageLiftLaw M := fun ν Γ ρ k e => by
  rw [him, him]
  exact denote_image_lift ν ρ k e

/-- At the actual interpretation `ImageBvarRelL` reduces to left
`.bot`-adjunction closure of the entry's relation — the named residual,
made explicit.  `hbot` is not derivable for arbitrary `R`; it holds for
relations between `.bot`-closed (`denI`-valued) arguments. -/
theorem bvarImageRelL_of_denoteImage {M : AnnSemantics}
    (him : ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (e : ExprA),
      M.image ν Γ ρ e = UnitModel.denote ν ρ e)
    (hbot : ∀ (R : Relation) (x W : Value),
      R x W → R (fun c => c = .bot ∨ x c) W) :
    ImageBvarRelL M := fun ν Γ ρ i R x W hx hR => by
  subst hx
  rw [him, denote_image_bvar]
  exact hbot _ _ _ hR

/-- The right-argument analogue. -/
theorem bvarImageRelR_of_denoteImage {M : AnnSemantics}
    (him : ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (e : ExprA),
      M.image ν Γ ρ e = UnitModel.denote ν ρ e)
    (hbot : ∀ (R : Relation) (W y : Value),
      R W y → R W (fun c => c = .bot ∨ y c)) :
    ImageBvarRelR M := fun ν Γ ρ i R W y hy hR => by
  subst hy
  rw [him, denote_image_bvar]
  exact hbot _ _ _ hR

end ImageLaws

section Lookup

/-- Paired entry extraction at an assumption declaration: the `i`-th
`EnvI.cons` layer stores related entries `x`, `y`, and the declared type
`A` has a `CodePair` in the `i+1`-dropped tail environments. -/
theorem pairedRealises_entry_assumption {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI}
    (h : PairedRealises M ν μ Γ ρ σ) :
    ∀ {i : Nat} {A : ExprA}, Γ.get? i = some (.assumption A) →
    ∃ (x y : Value) (k : Option Nat) (R S : Relation),
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) A)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) A) R S := by
  induction h with
  | nil ρ σ => intro i A hget; nomatch hget
  | @assumption Γᵢ ρᵢ σᵢ Aᵢ x y k R S tail codes related ih =>
    intro i A' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.assumption Aᵢ :: Γᵢ).get? 0 =
          some (.assumption Aᵢ) := rfl
      rw [hz] at hget
      obtain rfl : Aᵢ = A' := by simpa using hget
      exact ⟨x, y, k, R, S, rfl, rfl, related, codes⟩
    | succ j => exact ih hget
  | @letBinding Γᵢ ρᵢ σᵢ Aᵢ vᵢ x y k R S tail codes related lv rv ih =>
    intro i A' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.letBinding Aᵢ vᵢ :: Γᵢ).get? 0 =
          some (.letBinding Aᵢ vᵢ) := rfl
      rw [hz] at hget
      exact LocalDeclA.noConfusion (Option.some.inj hget)
    | succ j => exact ih hget

/-- Paired entry extraction at a stored-let declaration: additionally the
two stored-value agreements of the entry, in the dropped tail
environments (`right_value` is stated at the right relation `S`). -/
theorem pairedRealises_entry_letBinding {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI}
    (h : PairedRealises M ν μ Γ ρ σ) :
    ∀ {i : Nat} {A v : ExprA}, Γ.get? i = some (.letBinding A v) →
    ∃ (x y : Value) (k : Option Nat) (R S : Relation),
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) A)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) A) R S ∧
      R x (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) v) ∧
      S y (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) v) := by
  induction h with
  | nil ρ σ => intro i A v hget; nomatch hget
  | @assumption Γᵢ ρᵢ σᵢ Aᵢ x y k R S tail codes related ih =>
    intro i A' v' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.assumption Aᵢ :: Γᵢ).get? 0 =
          some (.assumption Aᵢ) := rfl
      rw [hz] at hget
      exact LocalDeclA.noConfusion (Option.some.inj hget)
    | succ j => exact ih hget
  | @letBinding Γᵢ ρᵢ σᵢ Aᵢ vᵢ x y k R S tail codes related lv rv ih =>
    intro i A' v' hget
    cases i with
    | zero =>
      have hz : (LocalDeclA.letBinding Aᵢ vᵢ :: Γᵢ).get? 0 =
          some (.letBinding Aᵢ vᵢ) := rfl
      rw [hz] at hget
      obtain ⟨rfl, rfl⟩ : Aᵢ = A' ∧ vᵢ = v' := by simpa using hget
      exact ⟨x, y, k, R, S, rfl, rfl, related, codes, lv, rv⟩
    | succ j => exact ih hget

/-- Paired lookup at `lookupTypeA`: whatever its declaration shape, the
`i`-th entry contributes related values `x`, `y` (`ρ i = x`, `σ i = y`)
and a `CodePair` for the stored (unlifted) type in the tail
environments.  The lifted result `A = liftA 0 (i+1) a` is returned so
consumers can transport via `ImageLiftLaw`. -/
theorem pairedRealises_lookupType {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {i : Nat} {A : ExprA}
    (h : PairedRealises M ν μ Γ ρ σ) (hlook : lookupTypeA Γ i = some A) :
    ∃ (a : ExprA) (x y : Value) (k : Option Nat) (R S : Relation),
      A = liftA 0 (i + 1) a ∧ ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) a)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) a) R S := by
  unfold lookupTypeA at hlook
  cases hd : Γ.get? i with
  | none => rw [hd] at hlook; nomatch hlook
  | some d =>
    cases d with
    | assumption a =>
      rw [hd] at hlook
      simp only [Option.some.injEq] at hlook
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc⟩ :=
        pairedRealises_entry_assumption h hd
      exact ⟨a, x, y, k, R, S, hlook.symm, hx, hy, hrel, hc⟩
    | letBinding a v =>
      rw [hd] at hlook
      simp only [Option.some.injEq] at hlook
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc, -, -⟩ :=
        pairedRealises_entry_letBinding h hd
      exact ⟨a, x, y, k, R, S, hlook.symm, hx, hy, hrel, hc⟩

/-- Paired lookup at a stored-let: `lookupValueA`/`lookupTypeA` expose
the stored value's two agreements and the declared type's `CodePair`,
all in the `i+1`-dropped tail environments. -/
theorem pairedRealises_lookupValueType {M : AnnSemantics} {ν μ : Valuation}
    {Γ : LCtxA} {ρ σ : EnvI} {i : Nat} {A v : ExprA}
    (h : PairedRealises M ν μ Γ ρ σ)
    (hval : lookupValueA Γ i = some v) (hty : lookupTypeA Γ i = some A) :
    ∃ (a vd : ExprA) (x y : Value) (k : Option Nat) (R S : Relation),
      A = liftA 0 (i + 1) a ∧ v = liftA 0 (i + 1) vd ∧
      ρ i = x ∧ σ i = y ∧ R x y ∧
      CodePair M.toCodeSystem k
        (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) a)
        (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) a) R S ∧
      R x (M.image ν (Γ.drop (i + 1)) (EnvI.drop ρ (i + 1)) vd) ∧
      S y (M.image μ (Γ.drop (i + 1)) (EnvI.drop σ (i + 1)) vd) := by
  unfold lookupValueA at hval
  unfold lookupTypeA at hty
  cases hd : Γ.get? i with
  | none => rw [hd] at hval; nomatch hval
  | some d =>
    cases d with
    | assumption a => rw [hd] at hval; nomatch hval
    | letBinding a vd =>
      rw [hd] at hval
      rw [hd] at hty
      simp only [Option.some.injEq] at hval hty
      obtain ⟨x, y, k, R, S, hx, hy, hrel, hc, hlv, hrv⟩ :=
        pairedRealises_entry_letBinding h hd
      exact ⟨a, vd, x, y, k, R, S, hty.symm, hval.symm, hx, hy, hrel, hc,
        hlv, hrv⟩

end Lookup

section Arms

/-- `PairedArms.Ty_bvar`, supplied under `ImageLiftLaw` and the two
entry-relatedness laws.  **Conditional consumer (measurement), not a
discharge**: `ImageBvarRelL`/`ImageBvarRelR` are the named residual —
at the actual interpretation they are `.bot`-adjunction closure of the
assigned code relations (`bvarImageRelL_of_denoteImage`).

The entry's stored `CodePair` is transported to the lookup type via
`ImageLiftLaw`; relatedness `R x y` is carried to both `.bvar` images by
the two `ImageBvarRel` laws.  The `HasTyA` premise, child IH, `CtxWfA`,
and `ValuationRel` are unconsumed — the entry's code pair is the data. -/
theorem paired_ty_bvar_of_laws {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hlift : ImageLiftLaw M) (hbL : ImageBvarRelL M) (hbR : ImageBvarRelR M) :
    PairedArms.Ty_bvar M E I n := by
  intro Γ i A u hlook _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, x, y, k, R, S, hA, hx, hy, hrel, hcode⟩ :=
    pairedRealises_lookupType hreal hlook
  subst hA
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · rw [hlift]
    exact hcode.left_code
  · rw [hlift]
    exact hcode.right_code
  · exact hbR μ Γ σ i R _ y hy
      (hbL ν Γ ρ i R x y hx hrel)

/-- `PairedArms.Conv_zetaLocal`, supplied under `ImageLiftLaw` and the
left entry-relatedness law.  **Conditional consumer (measurement), not
a discharge** — `ImageBvarRelL` is the named residual, at the actual
interpretation left `.bot`-adjunction closure
(`bvarImageRelL_of_denoteImage`).

The goal `R (image ν (.bvar i)) (image μ v)` is obtained from the entry:
`R x y` (`related`) composed with `R y (image μ tail v)` (`right_value`
transported to `R` via `codes.transport`) gives `R x (image μ tail v)` by
`Laws.trans` of the entry code's laws; `ImageBvarRelL` carries it across
the variable image and `ImageLiftLaw` transports the stored value into
the full context. -/
theorem paired_conv_zetaLocal_of_laws {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (hlift : ImageLiftLaw M) (hbL : ImageBvarRelL M) :
    PairedArms.Conv_zetaLocal M E I n := by
  intro Γ i A v hval hty _htype _ih _hwf ν μ ρ σ _hνμ hreal
  obtain ⟨a, vd, x, y, k, R, S, hA, hv, hx, hy, hrel, hcode, _hlv, hrv⟩ :=
    pairedRealises_lookupValueType hreal hval hty
  subst hA
  subst hv
  refine ⟨k, R, S, ⟨?_, ?_, hcode.transport⟩, ?_⟩
  · rw [hlift]
    exact hcode.left_code
  · rw [hlift]
    exact hcode.right_code
  · rw [hlift]
    exact hbL ν Γ ρ i R x _ hx
      ((M.lawful hcode.left_code).trans hrel (hcode.to_left hrv))

/-- Convenience: `Ty_bvar` directly against the actual `denote`/
`translate` interpretation, with only the relation-side `.bot`-closure
residuals exposed.  `hbotL`/`hbotR` are the named unsupplied conditions:
closure of the code relation under `.bot`-adjunction of the stored
entry.  They hold for relations between `.bot`-closed values, which is
the shape every `denI`-built environment has; `AnnSemantics` itself does
not record it. -/
theorem paired_ty_bvar_of_denoteImage {M : AnnSemantics} {E : ResolvedEnvA}
    {I : IotaIfaceA} {n : Nat}
    (him : ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (e : ExprA),
      M.image ν Γ ρ e = UnitModel.denote ν ρ e)
    (hbotL : ∀ (R : Relation) (x W : Value),
      R x W → R (fun c => c = .bot ∨ x c) W)
    (hbotR : ∀ (R : Relation) (W y : Value),
      R W y → R W (fun c => c = .bot ∨ y c)) :
    PairedArms.Ty_bvar M E I n :=
  paired_ty_bvar_of_laws (imageLiftLaw_of_denoteImage him)
    (bvarImageRelL_of_denoteImage him hbotL)
    (bvarImageRelR_of_denoteImage him hbotR)

/-- Convenience: `Conv_zetaLocal` directly against the actual
interpretation, with only the left `.bot`-closure residual exposed. -/
theorem paired_conv_zetaLocal_of_denoteImage {M : AnnSemantics}
    {E : ResolvedEnvA} {I : IotaIfaceA} {n : Nat}
    (him : ∀ (ν : Valuation) (Γ : LCtxA) (ρ : EnvI) (e : ExprA),
      M.image ν Γ ρ e = UnitModel.denote ν ρ e)
    (hbot : ∀ (R : Relation) (x W : Value),
      R x W → R (fun c => c = .bot ∨ x c) W) :
    PairedArms.Conv_zetaLocal M E I n :=
  paired_conv_zetaLocal_of_laws (imageLiftLaw_of_denoteImage him)
    (bvarImageRelL_of_denoteImage him hbot)

end Arms

#print axioms ImageLiftLaw
#print axioms ImageBvarRelL
#print axioms ImageBvarRelR
#print axioms denote_image_bvar
#print axioms denote_image_lift
#print axioms imageLiftLaw_of_denoteImage
#print axioms bvarImageRelL_of_denoteImage
#print axioms bvarImageRelR_of_denoteImage
#print axioms pairedRealises_entry_assumption
#print axioms pairedRealises_entry_letBinding
#print axioms pairedRealises_lookupType
#print axioms pairedRealises_lookupValueType
#print axioms paired_ty_bvar_of_laws
#print axioms paired_conv_zetaLocal_of_laws
#print axioms paired_ty_bvar_of_denoteImage
#print axioms paired_conv_zetaLocal_of_denoteImage

end Rcic.Declarative.Ann.LR3.PairedLookup
