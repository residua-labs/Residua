import rcic.RcicTypedJD

/-!
# R-NoDeltaRec-4d-v — the typed chain rows as a consumable interface, at the D-judgment

`RcicTypedRowsWf`'s twin on the D-judgment (`RcicTypedJD`): the same three chain rows, stated
on `TyConvTD`/`CtxWfTD`/`ConvArgsTD` over the annotated environment `EA`. The member reads are
annotated (`EA.members r = some m`, `m : CheckedMemberA`, the telescope instantiation erasing
`m.mtypeA`), so the D-interface needs no `eraseMember` transport — and no `EnvNormEraseA`,
whose whole job was making the erased environment's ι the copy's; the D-judgment's ι is
`DerivedIotaN` already.

The interface carries NO supply-side hypotheses (no `AnnEnvA`, no `IotaSRA`, no norm-erasure
premise, and no positive "success" evidence), exactly as `TypedRowsWf`. The supplier is
`RcicAnnRowsSupplyD.typedRowsWfD_of_annEnvA`.
-/

namespace Rcic.Declarative.Ann

open Rcic.Declarative

/-- A `TyConvTD` chain is pure reflexivity, or has a first conversion step at a sort with the
    rest of the chain after it — `TyConvT.firstOf`'s twin. -/
theorem TyConvTD.firstOf {EA : ResolvedEnvA} {n : Nat} {Γ : LCtx} {A B : Expr Nat}
    (h : TyConvTD EA n Γ A B) : (A = B) ∨
      ∃ C u, Nonempty (ConvTD EA n Γ A C (.sort u)) ∧ Nonempty (TyConvTD EA n Γ C B) := by
  induction h with
  | refl => exact Or.inl rfl
  | of _ _ u h => exact Or.inr ⟨_, u, ⟨h⟩, ⟨TyConvTD.refl _ _⟩⟩
  | trans _ _ _ h1 h2 ih1 ih2 =>
      rcases ih1 with he | ⟨C, u, ⟨h⟩, ⟨rest⟩⟩
      · exact he ▸ ih2
      · exact Or.inr ⟨C, u, ⟨h⟩, ⟨TyConvTD.trans _ _ _ _ rest h2⟩⟩

/-- GLM-1's interface at the D-judgment: the three rows, `TyConvTD`-primary, existence-valued,
    `CtxWfTD`-conditioned per call — `TypedRowsWf`'s twin, `EnvNormEraseA`-free. -/
structure TypedRowsWfD (EA : ResolvedEnvA) (n : Nat) : Prop where
  /-- ROW 1: convertible sorts are `=ₙ`, from the chain alone. -/
  sortRow : ∀ {Γ : LCtx}, CtxWfTD EA n Γ → ∀ {u v : Level},
    TyConvTD EA n Γ (.sort u) (.sort v) → eqN u v
  /-- ROW 2: convertible Π's have type-convertible domains and, under the left domain,
      type-convertible codomains, in existence form. -/
  piRow : ∀ {Γ : LCtx}, CtxWfTD EA n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvTD EA n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvTD EA n Γ A A') ∧ Nonempty (TyConvTD EA n (.assumption A :: Γ) B B')
  /-- ROW 3: at a real family lookup and class, with the left full application typed at a
      sort, a chain between two full applications has `=ₙ` levels, equal lengths and
      pointwise `ConvArgsTD` along the LEFT instantiation of the member's stored type
      (erased — `TypedRowsWf.famAppRow`'s twin; the member is already annotated). -/
  famAppRow : ∀ {Γ : LCtx}, CtxWfTD EA n Γ → ∀ {r : Nat} {m : CheckedMemberA}
      {ls ls' : List Level} {xs xs' : List (Expr Nat)} {w : Level}
      (hm : EA.members r = some m) (hind : m.mclass = .inductiveM)
      (hty : HasTyTD EA n Γ (foldApps (.const r ls) xs) (.sort w))
      (h : TyConvTD EA n Γ (foldApps (.const r ls) xs) (foldApps (.const r ls') xs')),
      eqNList ls ls' ∧ xs.length = xs'.length ∧
        ConvArgsTD EA n Γ (instantiateLevels ls (erase m.mtypeA)) xs xs'

/-- ROW 2's field as a standalone hypothesis — `PiRowField`'s twin. -/
def PiRowFieldD (EA : ResolvedEnvA) (n : Nat) : Prop :=
  ∀ {Γ : LCtx}, CtxWfTD EA n Γ → ∀ {A B A' B' : Expr Nat},
    TyConvTD EA n Γ (.pi A B) (.pi A' B') →
    Nonempty (TyConvTD EA n Γ A A') ∧ Nonempty (TyConvTD EA n (.assumption A :: Γ) B B')

/-- `TypedRowsWfD.piRow` is a `PiRowFieldD`. -/
def PiRowFieldD.of_typedRowsWfD {EA : ResolvedEnvA} {n : Nat} (t : TypedRowsWfD EA n) :
    PiRowFieldD EA n :=
  t.piRow

end Rcic.Declarative.Ann

#print axioms Rcic.Declarative.Ann.TypedRowsWfD
#print axioms Rcic.Declarative.Ann.TyConvTD.firstOf
