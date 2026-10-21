import rcic.RcicTypedJ

/-!
# M3-b GLM-1 — the typed chain rows as a consumable interface

`RcicAnnTypedRows` / `RcicAnnIotaSR` prove the three rows on the typed judgment
(`sortConvCharT'`, `piConvInjT'`, `famAppConvInjT_any'`) at a SINGLE `ConvT` at one
type. The consumers GLM-2 migrates (`RcicDTMeta`, `RcicParRedSR`, `RcicMachineSound`,
the `_of_rows` faces) hold a TYPE-CONVERSION CHAIN `TyConvT` between the two ends,
with no distinguished intermediate type. This module states the low-level interface
those consumers can call: `TypedRowsWf`, three fields, `TyConvT`-primary,
existence-valued where the data cannot be extracted (M3-b-0 O5), `CtxWfT` conditioned
per call site.

The interface carries NO supply-side hypotheses (no `AnnEnvA`, no `RowsT`, no
`EnvSemA`, no `IotaSRA`, no `NoParamsA`, and no positive "success" evidence). The
supplier is `RcicAnnRowsSupply.typedRowsWf_of_annEnvA`; the negative controls and
non-vacuity pins are `RcicTypedRowsSupplyPins`.

Field reading:
* ROW 1 (sort): a chain between two sorts collapses to `eqN` — no typing premise
  needed, the left sort is typed at its successor sort by the judgment's own `sort`
  rule.
* ROW 2 (pi): a chain between two Π's yields EXISTENCE of the domain chain and of the
  codomain chain under the left domain. A pure-refl chain outputs two refls directly
  (a refl chain carries no typing; none is invented). A chain with a real step is
  collapsed to one conversion at the left Π's own sort and read by the fixed-type row.
* ROW 3 (family): at a real family lookup and class, with the LEFT full application
  typed at a sort (the typing the consumer of a typed chain already holds), a chain
  between the two full applications yields `eqNList`, equal lengths, and pointwise
  `ConvArgsT` along the LEFT instantiation of the member's stored type. The family's
  SHAPE (its stored type's body is a sort) is recovered by the SUPPLIER from the
  admission, not smuggled into the interface.
-/

namespace Rcic.Declarative

/-- A `TyConvT` chain is pure reflexivity, or has a first conversion step at a sort
    with the rest of the chain after it. Pure judgment-side; used to give the pure-refl
    chains of rows 1–2 their direct reading and every other chain its collapse. -/
theorem TyConvT.firstOf {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (h : TyConvT E n Γ A B) : (A = B) ∨
      ∃ C u, Nonempty (ConvT E n Γ A C (.sort u)) ∧ Nonempty (TyConvT E n Γ C B) := by
  induction h with
  | refl => exact Or.inl rfl
  | of _ _ u h => exact Or.inr ⟨_, u, ⟨h⟩, ⟨TyConvT.refl _ _⟩⟩
  | trans _ _ _ h1 h2 ih1 ih2 =>
      rcases ih1 with he | ⟨C, u, ⟨h⟩, ⟨rest⟩⟩
      · exact he ▸ ih2
      · exact Or.inr ⟨C, u, ⟨h⟩, ⟨TyConvT.trans _ _ _ _ rest h2⟩⟩

/-- GLM-1's interface: the three rows, `TyConvT`-primary, existence-valued,
    `CtxWfT`-conditioned per call. Prop-valued (the consumers eliminate the
    existentials inside Prop; no runtime data is extracted). -/
structure TypedRowsWf (E : ResolvedEnv) (n : Nat) : Prop where
  /-- ROW 1: convertible sorts are `=ₙ`, from the chain alone. -/
  sortRow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {u v : Level},
    TyConvT E n Γ (.sort u) (.sort v) → eqN u v
  /-- ROW 2: convertible Π's have type-convertible domains and, under the left domain,
      type-convertible codomains, in existence form. -/
  piRow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B')
  /-- ROW 3: at a real family lookup and class, with the left full application typed
      at a sort, a chain between two full applications has `=ₙ` levels, equal lengths
      and pointwise `ConvArgsT` along the LEFT instantiation of the stored type. -/
  famAppRow : ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {r : Nat} {m : CheckedMember}
      {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
      (hm : E.members r = some m) (hind : m.mclass = .inductiveM)
      (hty : HasTyT E n Γ (foldApps (.const r ls) xs) (.sort w))
      (h : TyConvT E n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')),
      eqNList ls ls' ∧ xs.length = xs'.length ∧
        ConvArgsT E n Γ (instantiateLevels ls m.mtype) xs xs'

/-- ROW 2's field as a standalone hypothesis: `TypedRowsWf.piRow`'s exact
    type, so consumers that need only the Π row (spine inversion, the
    famApp left-instantiation walk) can be stated against the field itself
    rather than a full `TypedRowsWf` (which is exactly what is being
    constructed). -/
def PiRowField (E : ResolvedEnv) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfT E n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvT E n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvT E n Γ A A') ∧ Nonempty (TyConvT E n (.assumption A :: Γ) B B')

/-- `TypedRowsWf.piRow` is a `PiRowField`. -/
def PiRowField.of_typedRowsWf {E : ResolvedEnv} {n : Nat} (t : TypedRowsWf E n) :
    PiRowField E n :=
  t.piRow

end Rcic.Declarative

#print axioms Rcic.Declarative.TypedRowsWf
#print axioms Rcic.Declarative.TyConvT.firstOf
