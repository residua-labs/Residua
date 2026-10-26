import rcic.RcicFamAppRevFamRow
import rcic.RcicFamAppRevFixture
import rcic.RcicClassCRevealedLok

/-!
# RcicFamAppRevLok — level-bounded transfer (`LOKc`), generic internal injectivity, and diagonal-ι analysis for `RevEnv`

For the tier's F3 class-B1 condition (cc 10-25 01:20Z addendum; `cc-riskexplorer` Cycle 39 gaps α and β),
this module measures and proves the level-bound (`LOKt` / `LOKc` / `LOKtc`, `RcicF3Defs`) and ι-witness
properties of both index-injectivity producers on ANY revealed singleton `R : RevEnv`:

1. **Exact `LOK` preservation on the way back (`R.twin₁ → R.E`)**:
   `bkTyB`, `bkConvB`, `bkTyConvB` are the `Type`-valued back-translations from the recursor-free
   copy-only twin `R.twin₁` to `R.E`. Because `R.twin₁` places the constructor axiom at the constructor's
   own reference `R.f + 1` and agrees with `R.E` everywhere else, every constructor of `HasTyT` / `ConvT` /
   `TyConvT` maps 1-to-1 with identical level arguments and constant references:
   - `lok_bkTyB : LOKt σ N K (R.bkTyB d) ↔ LOKt σ N K d`
   - `lok_bkConvB : LOKc σ N K (R.bkConvB c) ↔ LOKc σ N K c`
   - `lok_bkTyConvB : LOKtc σ N K (R.bkTyConvB hc) ↔ LOKtc σ N K hc`

2. **`LOK` preservation along the K-like cell and round trip (`e ≡ tr R.f R.I e`)**:
   `recTG_conv_recB` and `trConv_selfB` rebuild the K-like cell and round-trip conversion
   `ConvT R.E n Γ e (tr R.f R.I e) A` in `Type` with explicit `castHT`/`castCL`/`castCR` casts.
   Under `1 ≤ N`, `evalTotal σ R.uI ≤ N`, `K (R.f + 2) + 1 ≤ N`, and `∀ Γ', LOKt σ N K (R.hIEB n Γ')`,
   `lok_trConv_selfB : LOKt σ N K d → LOKc σ N K (R.trConv_selfB d)`.

3. **Generic bounded internal injectivity (`rev_inj_internalB`, `rev_inj_internalB_lok`)**:
   Generalises `ri_inj_internalB` (`RcicClassCRevealedLok`) from `riEnv` (`I = Sort 0`) to EVERY
   revealed singleton `R : RevEnv` (including `Foo : Nat → Prop` with `I = Nat`) by instantiating the
   AnySort recursor `rec.{[R.uI]}` at the index sort `R.uI` with the constant motive
   `M₀ := λ (Y : R.I) (_ : F Y). R.I` and the identity minor `m₀ := λ (Y : R.I). Y`.
   Requires zero rows (`PiRowField` / `TypedRowsWf`) and carries `LOKc σ N K` directly from
   `LOKt σ N K hx`, `LOKt σ N K hx'`, and `LOKtc σ N K hc`.

4. **Structural ι-witness separation for gap β (`NoRecIota` / `DiagRecIota`)**:
   Unlike `rev_inj_internalB` (whose off-diagonal ι step has `preMajor = [M₀, m₀, x']` and `fields = [x]`,
   causing period zero in `RcicF3EqRIFixedPoint`), the copy-only twin route has:
   - `noRecIota_bkConvB : NoRecIota (R.f + 2) (R.bkConvB c)` — **zero** ι steps at the B1 recursor `R.f + 2`
     anywhere in the back-translated twin conversion;
   - `diagRecIota_trConv_selfB : DiagRecIotaTy (R.f + 2) d → DiagRecIota (R.f + 2) (R.trConv_selfB d)` —
     the round trip's K-like cell `kcellLB` uses only the **diagonal** ι witness
     `R.revWAt l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)` where `field = index = .bvar 1`.

closure_claim = 0.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Rcic.Syn.FamApp.Rev

open Rcic.Declarative
open Rcic.F3.PSet
open Rcic.Syn.ClassC
open Rcic.Syn.FamApp.RevTwin

/-! ## §0 Explicit index-cast helpers and ι wrapper -/

section CastHelpers

variable {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
variable {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

/-- Rewrite the context index of a typing derivation along an equality. -/
def castHTCtx {Γ' : LCtx} {e T : Expr Nat} (h : Γ = Γ') (d : HasTyT E n Γ e T) : HasTyT E n Γ' e T := h ▸ d

/-- Rewrite the term index of a typing derivation along an equality. -/
def castHTE {e e' T : Expr Nat} (h : e = e') (d : HasTyT E n Γ e T) : HasTyT E n Γ e' T := h ▸ d

/-- Rewrite the LHS of a conversion along an equality. -/
def castCL {a a' b T : Expr Nat} (h : a = a') (c : ConvT E n Γ a b T) : ConvT E n Γ a' b T := h ▸ c

/-- Rewrite the RHS of a conversion along an equality. -/
def castCR {a b b' T : Expr Nat} (h : b = b') (c : ConvT E n Γ a b T) : ConvT E n Γ a b' T := h ▸ c

@[simp] theorem LOKt_castHTCtx {Γ' : LCtx} {e T : Expr Nat} (h : Γ = Γ') (d : HasTyT E n Γ e T) :
    LOKt σ N K (castHTCtx h d) ↔ LOKt σ N K d := by
  subst h; exact Iff.rfl

@[simp] theorem LOKt_castHTE {e e' T : Expr Nat} (h : e = e') (d : HasTyT E n Γ e T) :
    LOKt σ N K (castHTE h d) ↔ LOKt σ N K d := by
  subst h; exact Iff.rfl

@[simp] theorem LOKc_castCL {a a' b T : Expr Nat} (h : a = a') (c : ConvT E n Γ a b T) :
    LOKc σ N K (castCL h c) ↔ LOKc σ N K c := by
  subst h; exact Iff.rfl

@[simp] theorem LOKc_castCR {a b b' T : Expr Nat} (h : b = b') (c : ConvT E n Γ a b T) :
    LOKc σ N K (castCR h c) ↔ LOKc σ N K c := by
  subst h; exact Iff.rfl

@[simp] theorem lok_bvar {i : Nat} {A : Expr Nat} (h : lookupType Γ i = some A) :
    LOKt σ N K (HasTyT.bvar (E := E) (n := n) Γ i A h) := by
  simp only [LOKt]

/-- Build a `.iota` conversion from a witness and endpoint equalities using explicit `castCL`/`castCR`/`castHTE`. -/
def iotaOfWitness {lhs rhs T : Expr Nat} (w : IotaWitness E)
    (hlhs : iotaLhsOf w = lhs) (hrhs : iotaRhsOf w = rhs)
    (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T) :
    ConvT E n Γ lhs rhs T :=
  castCL hlhs (castCR hrhs
    (.iota Γ (iotaLhsOf w) (iotaRhsOf w) T (.of w)
      (castHTE hlhs.symm hl) (castHTE hrhs.symm hr)))

@[simp] theorem lok_iotaOfWitness {lhs rhs T : Expr Nat} (w : IotaWitness E)
    (hlhs : iotaLhsOf w = lhs) (hrhs : iotaRhsOf w = rhs)
    (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T) :
    LOKc σ N K (iotaOfWitness w hlhs hrhs hl hr) ↔ (LOKt σ N K hl ∧ LOKt σ N K hr) := by
  subst hlhs; subst hrhs; exact Iff.rfl

end CastHelpers

/-! ## §0b Structural ι-witness predicates (`NoRecIota` / `DiagRecIota`) -/

section IotaPredicates

variable {E : ResolvedEnv} {n : Nat}

mutual
/-- No `.iota` step in a typing derivation uses recursor `r`. -/
def NoRecIotaTy (r : Nat) : {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, .sort _ _ => True
  | _, _, _, .bvar _ _ _ _ => True
  | _, _, _, .const _ _ _ _ _ _ _ => True
  | _, _, _, .pi _ _ _ _ _ hA hB => NoRecIotaTy r hA ∧ NoRecIotaTy r hB
  | _, _, _, .lam _ _ _ _ _ hA hb => NoRecIotaTy r hA ∧ NoRecIotaTy r hb
  | _, _, _, .app _ _ _ _ _ hf ha => NoRecIotaTy r hf ∧ NoRecIotaTy r ha
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => NoRecIotaTy r hA ∧ NoRecIotaTy r hv ∧ NoRecIotaTy r hb
  | _, _, _, .lit _ _ _ hexp => NoRecIotaTy r hexp
  | _, _, _, .conv _ _ _ _ _ h hc => NoRecIotaTy r h ∧ NoRecIota r hc

/-- No `.iota` step in a conversion derivation uses recursor `r`. -/
def NoRecIota (r : Nat) : {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → Prop
  | _, _, _, _, .refl _ _ _ h => NoRecIotaTy r h
  | _, _, _, _, .symm _ _ _ _ h => NoRecIota r h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => NoRecIota r h1 ∧ NoRecIota r h2
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha => NoRecIotaTy r hA ∧ NoRecIotaTy r hb ∧ NoRecIotaTy r ha
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => NoRecIotaTy r hA ∧ NoRecIotaTy r hv ∧ NoRecIotaTy r hb
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => NoRecIotaTy r hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => NoRecIotaTy r hb
  | _, _, _, _, .iota _ _ _ _ (.of w) hl hr => w.recRef ≠ r ∧ NoRecIotaTy r hl ∧ NoRecIotaTy r hr
  | _, _, _, _, .lit _ _ _ _ _ hexp => NoRecIotaTy r hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => NoRecIota r h1 ∧ NoRecIota r h2
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => NoRecIota r hA ∧ NoRecIota r hb
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => NoRecIota r hA ∧ NoRecIota r hB
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => NoRecIota r hA ∧ NoRecIota r hv ∧ NoRecIota r hb
  | _, _, _, _, .sorts _ _ _ _ => True
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => True
  | _, _, _, _, .eta _ _ _ _ h => NoRecIotaTy r h
  | _, _, _, _, .irr _ _ _ _ hP hp hq => NoRecIotaTy r hP ∧ NoRecIotaTy r hp ∧ NoRecIotaTy r hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => NoRecIota r h ∧ NoRecIota r hA
end

/-- A witness at recursor `r` is diagonal if whenever `w.recRef = r`, `w.preMajor = [M, m, X]` and `w.fields = [X]`
    for the SAME expression `X` (field = index). -/
def DiagWitnessAt (r : Nat) (w : IotaWitness E) : Prop :=
  w.recRef = r → ∃ M m X, w.preMajor = [M, m, X] ∧ w.fields = [X]

mutual
/-- Every `.iota` step at recursor `r` in a typing derivation is diagonal (`field = index`). -/
def DiagRecIotaTy (r : Nat) : {Γ : LCtx} → {e A : Expr Nat} → HasTyT E n Γ e A → Prop
  | _, _, _, .sort _ _ => True
  | _, _, _, .bvar _ _ _ _ => True
  | _, _, _, .const _ _ _ _ _ _ _ => True
  | _, _, _, .pi _ _ _ _ _ hA hB => DiagRecIotaTy r hA ∧ DiagRecIotaTy r hB
  | _, _, _, .lam _ _ _ _ _ hA hb => DiagRecIotaTy r hA ∧ DiagRecIotaTy r hb
  | _, _, _, .app _ _ _ _ _ hf ha => DiagRecIotaTy r hf ∧ DiagRecIotaTy r ha
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => DiagRecIotaTy r hA ∧ DiagRecIotaTy r hv ∧ DiagRecIotaTy r hb
  | _, _, _, .lit _ _ _ hexp => DiagRecIotaTy r hexp
  | _, _, _, .conv _ _ _ _ _ h hc => DiagRecIotaTy r h ∧ DiagRecIota r hc

/-- Every `.iota` step at recursor `r` in a conversion derivation is diagonal (`field = index`). -/
def DiagRecIota (r : Nat) : {Γ : LCtx} → {a b A : Expr Nat} → ConvT E n Γ a b A → Prop
  | _, _, _, _, .refl _ _ _ h => DiagRecIotaTy r h
  | _, _, _, _, .symm _ _ _ _ h => DiagRecIota r h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => DiagRecIota r h1 ∧ DiagRecIota r h2
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha => DiagRecIotaTy r hA ∧ DiagRecIotaTy r hb ∧ DiagRecIotaTy r ha
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => DiagRecIotaTy r hA ∧ DiagRecIotaTy r hv ∧ DiagRecIotaTy r hb
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => DiagRecIotaTy r hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => DiagRecIotaTy r hb
  | _, _, _, _, .iota _ _ _ _ (.of w) hl hr => DiagWitnessAt r w ∧ DiagRecIotaTy r hl ∧ DiagRecIotaTy r hr
  | _, _, _, _, .lit _ _ _ _ _ hexp => DiagRecIotaTy r hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => DiagRecIota r h1 ∧ DiagRecIota r h2
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => DiagRecIota r hA ∧ DiagRecIota r hb
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => DiagRecIota r hA ∧ DiagRecIota r hB
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => DiagRecIota r hA ∧ DiagRecIota r hv ∧ DiagRecIota r hb
  | _, _, _, _, .sorts _ _ _ _ => True
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ => True
  | _, _, _, _, .eta _ _ _ _ h => DiagRecIotaTy r h
  | _, _, _, _, .irr _ _ _ _ hP hp hq => DiagRecIotaTy r hP ∧ DiagRecIotaTy r hp ∧ DiagRecIotaTy r hq
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => DiagRecIota r h ∧ DiagRecIota r hA
end

@[simp] theorem diagRecIotaTy_bvar (r : Nat) {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Γ i = some A) :
    DiagRecIotaTy r (HasTyT.bvar (E := E) (n := n) Γ i A h) := by
  simp only [DiagRecIotaTy]

@[simp] theorem noRecIotaTy_castHT {r : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (h : T = T') (d : HasTyT E n Γ e T) :
    NoRecIotaTy r (castHT h d) ↔ NoRecIotaTy r d := by
  subst h; exact Iff.rfl

@[simp] theorem noRecIota_castT {r : Nat} {Γ : LCtx} {a b T T' : Expr Nat}
    (h : T = T') (c : ConvT E n Γ a b T) :
    NoRecIota r (castT h c) ↔ NoRecIota r c := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIotaTy_castHTCtx {r : Nat} {Γ Γ' : LCtx} {e T : Expr Nat}
    (h : Γ = Γ') (d : HasTyT E n Γ e T) :
    DiagRecIotaTy r (castHTCtx h d) ↔ DiagRecIotaTy r d := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIotaTy_castHT {r : Nat} {Γ : LCtx} {e T T' : Expr Nat}
    (h : T = T') (d : HasTyT E n Γ e T) :
    DiagRecIotaTy r (castHT h d) ↔ DiagRecIotaTy r d := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIotaTy_castHTE {r : Nat} {Γ : LCtx} {e e' T : Expr Nat}
    (h : e = e') (d : HasTyT E n Γ e T) :
    DiagRecIotaTy r (castHTE h d) ↔ DiagRecIotaTy r d := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIota_castT {r : Nat} {Γ : LCtx} {a b T T' : Expr Nat}
    (h : T = T') (c : ConvT E n Γ a b T) :
    DiagRecIota r (castT h c) ↔ DiagRecIota r c := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIota_castCL {r : Nat} {Γ : LCtx} {a a' b T : Expr Nat}
    (h : a = a') (c : ConvT E n Γ a b T) :
    DiagRecIota r (castCL h c) ↔ DiagRecIota r c := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIota_castCR {r : Nat} {Γ : LCtx} {a b b' T : Expr Nat}
    (h : b = b') (c : ConvT E n Γ a b T) :
    DiagRecIota r (castCR h c) ↔ DiagRecIota r c := by
  subst h; exact Iff.rfl

@[simp] theorem diagRecIota_iotaOfWitness {r : Nat} {Γ : LCtx} {lhs rhs T : Expr Nat}
    (w : IotaWitness E) (hlhs : iotaLhsOf w = lhs) (hrhs : iotaRhsOf w = rhs)
    (hl : HasTyT E n Γ lhs T) (hr : HasTyT E n Γ rhs T) :
    DiagRecIota r (iotaOfWitness w hlhs hrhs hl hr) ↔
      (DiagWitnessAt r w ∧ DiagRecIotaTy r hl ∧ DiagRecIotaTy r hr) := by
  subst hlhs; subst hrhs; exact Iff.rfl

mutual
theorem diagRecIotaTy_of_noRecIotaTy {r : Nat} :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT E n Γ e A) →
    NoRecIotaTy r d → DiagRecIotaTy r d
  | _, _, _, .sort _ _, _ => trivial
  | _, _, _, .bvar _ _ _ _, _ => trivial
  | _, _, _, .const _ _ _ _ _ _ _, _ => trivial
  | _, _, _, .pi _ _ _ _ _ hA hB, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hA hd.1, diagRecIotaTy_of_noRecIotaTy hB hd.2⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hA hd.1, diagRecIotaTy_of_noRecIotaTy hb hd.2⟩
  | _, _, _, .app _ _ _ _ _ hf ha, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hf hd.1, diagRecIotaTy_of_noRecIotaTy ha hd.2⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hA hd.1, diagRecIotaTy_of_noRecIotaTy hv hd.2.1,
        diagRecIotaTy_of_noRecIotaTy hb hd.2.2⟩
  | _, _, _, .lit _ _ _ hexp, h => diagRecIotaTy_of_noRecIotaTy hexp h
  | _, _, _, .conv _ _ _ _ _ h hc, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy h hd.1, diagRecIota_of_noRecIota hc hd.2⟩

theorem diagRecIota_of_noRecIota {r : Nat} :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT E n Γ a b A) →
    NoRecIota r c → DiagRecIota r c
  | _, _, _, _, .refl _ _ _ h, h1 => diagRecIotaTy_of_noRecIotaTy h h1
  | _, _, _, _, .symm _ _ _ _ h, h1 => diagRecIota_of_noRecIota h h1
  | _, _, _, _, .trans _ _ _ _ _ h1 h2, hd =>
      ⟨diagRecIota_of_noRecIota h1 hd.1, diagRecIota_of_noRecIota h2 hd.2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hA hd.1, diagRecIotaTy_of_noRecIotaTy hb hd.2.1,
        diagRecIotaTy_of_noRecIotaTy ha hd.2.2⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hA hd.1, diagRecIotaTy_of_noRecIotaTy hv hd.2.1,
        diagRecIotaTy_of_noRecIotaTy hb hd.2.2⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv, h1 => diagRecIotaTy_of_noRecIotaTy hv h1
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb, h1 => diagRecIotaTy_of_noRecIotaTy hb h1
  | _, _, _, _, .iota _ _ _ _ (.of _) hl hr, hd =>
      ⟨fun he => absurd he hd.1, diagRecIotaTy_of_noRecIotaTy hl hd.2.1,
        diagRecIotaTy_of_noRecIotaTy hr hd.2.2⟩
  | _, _, _, _, .lit _ _ _ _ _ hexp, h1 => diagRecIotaTy_of_noRecIotaTy hexp h1
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2, hd =>
      ⟨diagRecIota_of_noRecIota h1 hd.1, diagRecIota_of_noRecIota h2 hd.2⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb, hd =>
      ⟨diagRecIota_of_noRecIota hA hd.1, diagRecIota_of_noRecIota hb hd.2⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB, hd =>
      ⟨diagRecIota_of_noRecIota hA hd.1, diagRecIota_of_noRecIota hB hd.2⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb, hd =>
      ⟨diagRecIota_of_noRecIota hA hd.1, diagRecIota_of_noRecIota hv hd.2.1,
        diagRecIota_of_noRecIota hb hd.2.2⟩
  | _, _, _, _, .sorts _ _ _ _, _ => trivial
  | _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _, _ => trivial
  | _, _, _, _, .eta _ _ _ _ h, h1 => diagRecIotaTy_of_noRecIotaTy h h1
  | _, _, _, _, .irr _ _ _ _ hP hp hq, hd =>
      ⟨diagRecIotaTy_of_noRecIotaTy hP hd.1, diagRecIotaTy_of_noRecIotaTy hp hd.2.1,
        diagRecIotaTy_of_noRecIotaTy hq hd.2.2⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA, hd =>
      ⟨diagRecIota_of_noRecIota h hd.1, diagRecIota_of_noRecIota hA hd.2⟩
end

end IotaPredicates

namespace RevEnv

variable (R : RevEnv) {n : Nat}

/-! ## §1 `Type`-valued back-translation `R.twin₁ → R.E` and exact `LOK` + `NoRecIota` preservation -/

section BackB

variable {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

/-- `Type`-valued constant typing transport `R.twin₁ → R.E`. -/
def bkConstB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    HasTyT R.E n Γ (.const r ls) (instantiateLevels ls m.mtype) :=
  if h1 : r = R.f + 1 then
    have hm : m = revAxM R.f R.I := by rw [h1, R.twin₁_f1] at hres; exact (Option.some.inj hres).symm
    castHT (by rw [hm]; rfl)
      (.const Γ r ls (revCtorM R.f R.I) (by rw [h1]; exact R.hEf1) (by rw [hm] at hlen; exact hlen) hwf)
  else if h0 : r = R.f then
    have hm : m = revFamM R.I := by rw [h0, R.twin₁_f] at hres; exact (Option.some.inj hres).symm
    castHT (by rw [hm])
      (.const Γ r ls (revFamM R.I) (by rw [h0]; exact R.hEf) (by rw [hm] at hlen; exact hlen) hwf)
  else
    have hlt : r < R.f := by
      rcases R.twin₁_class hres with ⟨hlt, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
      · exact hlt
      · exact absurd he h0
      · exact absurd he h1
    .const Γ r ls m (by rw [← R.twin₁_agree r hlt]; exact hres) hlen hwf

/-- `Type`-valued constant conversion transport `R.twin₁ → R.E`. -/
def bkConstsB (Γ : LCtx) (r : Nat) (ls ls' : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls') :
    ConvT R.E n Γ (.const r ls) (.const r ls') (instantiateLevels ls m.mtype) :=
  if h1 : r = R.f + 1 then
    have hm : m = revAxM R.f R.I := by rw [h1, R.twin₁_f1] at hres; exact (Option.some.inj hres).symm
    castT (by rw [hm]; rfl)
      (.consts Γ r ls ls' (revCtorM R.f R.I) (by rw [h1]; exact R.hEf1)
        (by rw [hm] at hlen; exact hlen) hwf hwf' h)
  else if h0 : r = R.f then
    have hm : m = revFamM R.I := by rw [h0, R.twin₁_f] at hres; exact (Option.some.inj hres).symm
    castT (by rw [hm])
      (.consts Γ r ls ls' (revFamM R.I) (by rw [h0]; exact R.hEf)
        (by rw [hm] at hlen; exact hlen) hwf hwf' h)
  else
    have hlt : r < R.f := by
      rcases R.twin₁_class hres with ⟨hlt, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
      · exact hlt
      · exact absurd he h0
      · exact absurd he h1
    .consts Γ r ls ls' m (by rw [← R.twin₁_agree r hlt]; exact hres) hlen hwf hwf' h

theorem lok_bkConstB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    LOKt σ N K (R.bkConstB Γ r ls m hres hlen hwf) ↔ LevelsOK σ (K r) ls := by
  unfold bkConstB
  split
  · simp only [LOKt_castHT, LOKt]
  · split <;> simp only [LOKt_castHT, LOKt]

theorem lok_bkConstsB (Γ : LCtx) (r : Nat) (ls ls' : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls') :
    LOKc σ N K (R.bkConstsB Γ r ls ls' m hres hlen hwf hwf' h) ↔
      (LevelsOK σ (K r) ls ∧ LevelsOK σ (K r) ls') := by
  unfold bkConstsB
  split
  · simp only [LOKc_castT, LOKc]
  · split <;> simp only [LOKc_castT, LOKc]

theorem noRecIotaTy_bkConstB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    NoRecIotaTy (R.f + 2) (R.bkConstB Γ r ls m hres hlen hwf) := by
  unfold bkConstB
  split
  · simp only [noRecIotaTy_castHT, NoRecIotaTy]
  · split <;> simp only [noRecIotaTy_castHT, NoRecIotaTy]

theorem noRecIota_bkConstsB (Γ : LCtx) (r : Nat) (ls ls' : List Level) (m : CheckedMember)
    (hres : R.twin₁.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) (hwf' : levelsBounded n ls' = true) (h : eqNList ls ls') :
    NoRecIota (R.f + 2) (R.bkConstsB Γ r ls ls' m hres hlen hwf hwf' h) := by
  unfold bkConstsB
  split
  · simp only [noRecIota_castT, NoRecIota]
  · split <;> simp only [noRecIota_castT, NoRecIota]

mutual
/-- `Type`-valued back-translation of typing derivations from the copy-only twin `R.twin₁` to `R.E`. -/
def bkTyB : {Γ : LCtx} → {e A : Expr Nat} → HasTyT R.twin₁ n Γ e A → HasTyT R.E n Γ e A
  | _, _, _, .sort Γ l => .sort Γ l
  | _, _, _, .bvar Γ i A h => .bvar Γ i A h
  | _, _, _, .const Γ r ls m hres hlen hwf => R.bkConstB Γ r ls m hres hlen hwf
  | _, _, _, .pi Γ A u B v hA hB => .pi Γ A u B v (bkTyB hA) (bkTyB hB)
  | _, _, _, .lam Γ A u body B hA hbody => .lam Γ A u body B (bkTyB hA) (bkTyB hbody)
  | _, _, _, .app Γ g a A B hf ha => .app Γ g a A B (bkTyB hf) (bkTyB ha)
  | _, _, _, .letE Γ A u value B body hA hv hb =>
      .letE Γ A u value B body (bkTyB hA) (bkTyB hv) (bkTyB hb)
  | _, _, _, .lit Γ t T hexp => .lit Γ t T (bkTyB hexp)
  | _, _, _, .conv Γ e A B u h hc => .conv Γ e A B u (bkTyB h) (bkConvB hc)

/-- `Type`-valued back-translation of conversion derivations from the copy-only twin `R.twin₁` to `R.E`. -/
def bkConvB : {Γ : LCtx} → {a b A : Expr Nat} → ConvT R.twin₁ n Γ a b A → ConvT R.E n Γ a b A
  | _, _, _, _, .refl Γ a A h => .refl Γ a A (bkTyB h)
  | _, _, _, _, .symm Γ a b A h => .symm Γ a b A (bkConvB h)
  | _, _, _, _, .trans Γ a b c A h1 h2 => .trans Γ a b c A (bkConvB h1) (bkConvB h2)
  | _, _, _, _, .beta Γ A body arg B u hA hbody harg =>
      .beta Γ A body arg B u (bkTyB hA) (bkTyB hbody) (bkTyB harg)
  | _, _, _, _, .zeta Γ A value body B u hA hv hb =>
      .zeta Γ A value body B u (bkTyB hA) (bkTyB hv) (bkTyB hb)
  | _, _, _, _, .zetaLocal Γ i A v hval hty hv =>
      .zetaLocal Γ i A v hval hty (bkTyB hv)
  | _, _, _, _, .delta Γ r ls m b hres hbody htr hlen hwf hb =>
      .delta Γ r ls m b (R.bkBody hres hbody) hbody htr hlen hwf (bkTyB hb)
  | _, _, _, _, .iota Γ lhs rhs T h hl hr =>
      .iota Γ lhs rhs T (R.bkIota h) (bkTyB hl) (bkTyB hr)
  | _, _, _, _, .lit Γ t exp T h hexp => .lit Γ t exp T h (bkTyB hexp)
  | _, _, _, _, .app Γ g g' a b A B h1 h2 => .app Γ g g' a b A B (bkConvB h1) (bkConvB h2)
  | _, _, _, _, .lam Γ A A' b b' B u hA hb => .lam Γ A A' b b' B u (bkConvB hA) (bkConvB hb)
  | _, _, _, _, .pi Γ A A' B B' u v hA hB => .pi Γ A A' B B' u v (bkConvB hA) (bkConvB hB)
  | _, _, _, _, .letE Γ A A' v v' b b' B u hA hv hb =>
      .letE Γ A A' v v' b b' B u (bkConvB hA) (bkConvB hv) (bkConvB hb)
  | _, _, _, _, .sorts Γ l₁ l₂ h => .sorts Γ l₁ l₂ h
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h =>
      R.bkConstsB Γ r ls ls' m hres hlen hwf hwf' h
  | _, _, _, _, .eta Γ g A B h => .eta Γ g A B (bkTyB h)
  | _, _, _, _, .irr Γ P p q hP hp hq => .irr Γ P p q (bkTyB hP) (bkTyB hp) (bkTyB hq)
  | _, _, _, _, .tyConv Γ a b A A' u h hA => .tyConv Γ a b A A' u (bkConvB h) (bkConvB hA)
end

/-- `Type`-valued back-translation of type-conversion chains from `R.twin₁` to `R.E`. -/
def bkTyConvB : {Γ : LCtx} → {a b : Expr Nat} → TyConvT R.twin₁ n Γ a b → TyConvT R.E n Γ a b
  | _, _, _, .refl Γ A => .refl Γ A
  | _, _, _, .of Γ A B u h => .of Γ A B u (R.bkConvB h)
  | _, _, _, .trans Γ A B C h1 h2 => .trans Γ A B C (bkTyConvB h1) (bkTyConvB h2)

mutual
/-- **`bkTyB` preserves `LOKt` with zero overhead.** -/
theorem lok_bkTyB :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT R.twin₁ n Γ e A) →
    (LOKt σ N K (R.bkTyB d) ↔ LOKt σ N K d)
  | _, _, _, .sort _ _ => by simp only [bkTyB, LOKt]
  | _, _, _, .bvar _ _ _ _ => by simp only [bkTyB, LOKt]
  | _, _, _, .const Γ r ls m hres hlen hwf => by
      simp only [bkTyB, LOKt]
      exact R.lok_bkConstB Γ r ls m hres hlen hwf
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      simp only [bkTyB, LOKt, lok_bkTyB hA, lok_bkTyB hB]
  | _, _, _, .lam _ _ _ _ _ hA hb => by
      simp only [bkTyB, LOKt, lok_bkTyB hA, lok_bkTyB hb]
  | _, _, _, .app _ _ _ _ _ hf ha => by
      simp only [bkTyB, LOKt, lok_bkTyB hf, lok_bkTyB ha]
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => by
      simp only [bkTyB, LOKt, lok_bkTyB hA, lok_bkTyB hv, lok_bkTyB hb]
  | _, _, _, .lit _ _ _ hexp => by
      simp only [bkTyB, LOKt, lok_bkTyB hexp]
  | _, _, _, .conv _ _ _ _ _ h hc => by
      simp only [bkTyB, LOKt, lok_bkTyB h, lok_bkConvB hc]

/-- **`bkConvB` preserves `LOKc` with zero overhead.** -/
theorem lok_bkConvB :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT R.twin₁ n Γ a b A) →
    (LOKc σ N K (R.bkConvB c) ↔ LOKc σ N K c)
  | _, _, _, _, .refl _ _ _ h => by simp only [bkConvB, LOKc, lok_bkTyB h]
  | _, _, _, _, .symm _ _ _ _ h => by simp only [bkConvB, LOKc, lok_bkConvB h]
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => by
      simp only [bkConvB, LOKc, lok_bkConvB h1, lok_bkConvB h2]
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha => by
      simp only [bkConvB, LOKc, lok_bkTyB hA, lok_bkTyB hb, lok_bkTyB ha]
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => by
      simp only [bkConvB, LOKc, lok_bkTyB hA, lok_bkTyB hv, lok_bkTyB hb]
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => by
      simp only [bkConvB, LOKc, lok_bkTyB hv]
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => by
      simp only [bkConvB, LOKc, lok_bkTyB hb]
  | _, _, _, _, .iota _ _ _ _ (.of _) hl hr => by
      simp only [bkConvB, bkIota, LOKc, lok_bkTyB hl, lok_bkTyB hr]
  | _, _, _, _, .lit _ _ _ _ _ hexp => by
      simp only [bkConvB, LOKc, lok_bkTyB hexp]
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => by
      simp only [bkConvB, LOKc, lok_bkConvB h1, lok_bkConvB h2]
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => by
      simp only [bkConvB, LOKc, lok_bkConvB hA, lok_bkConvB hb]
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => by
      simp only [bkConvB, LOKc, lok_bkConvB hA, lok_bkConvB hB]
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => by
      simp only [bkConvB, LOKc, lok_bkConvB hA, lok_bkConvB hv, lok_bkConvB hb]
  | _, _, _, _, .sorts _ _ _ _ => by simp only [bkConvB, LOKc]
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h => by
      simp only [bkConvB, LOKc]
      exact R.lok_bkConstsB Γ r ls ls' m hres hlen hwf hwf' h
  | _, _, _, _, .eta _ _ _ _ h => by simp only [bkConvB, LOKc, lok_bkTyB h]
  | _, _, _, _, .irr _ _ _ _ hP hp hq => by
      simp only [bkConvB, LOKc, lok_bkTyB hP, lok_bkTyB hp, lok_bkTyB hq]
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => by
      simp only [bkConvB, LOKc, lok_bkConvB h, lok_bkConvB hA]
end

/-- **`bkTyConvB` preserves `LOKtc` with zero overhead.** -/
theorem lok_bkTyConvB :
    {Γ : LCtx} → {a b : Expr Nat} → (hc : TyConvT R.twin₁ n Γ a b) →
    (LOKtc σ N K (R.bkTyConvB hc) ↔ LOKtc σ N K hc)
  | _, _, _, .refl _ _ => by simp only [bkTyConvB, LOKtc]
  | _, _, _, .of _ _ _ _ h => by simp only [bkTyConvB, LOKtc, R.lok_bkConvB h]
  | _, _, _, .trans _ _ _ _ h1 h2 => by
      simp only [bkTyConvB, LOKtc, lok_bkTyConvB h1, lok_bkTyConvB h2]

mutual
/-- **Every back-translated twin typing has ZERO ι steps at `R.f + 2`.** -/
theorem noRecIota_bkTyB :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT R.twin₁ n Γ e A) →
    NoRecIotaTy (R.f + 2) (R.bkTyB d)
  | _, _, _, .sort _ _ => by simp only [bkTyB, NoRecIotaTy]
  | _, _, _, .bvar _ _ _ _ => by simp only [bkTyB, NoRecIotaTy]
  | _, _, _, .const Γ r ls m hres hlen hwf => by
      simp only [bkTyB]
      exact R.noRecIotaTy_bkConstB Γ r ls m hres hlen hwf
  | _, _, _, .pi _ _ _ _ _ hA hB => by
      simp only [bkTyB, NoRecIotaTy]
      exact ⟨noRecIota_bkTyB hA, noRecIota_bkTyB hB⟩
  | _, _, _, .lam _ _ _ _ _ hA hb => by
      simp only [bkTyB, NoRecIotaTy]
      exact ⟨noRecIota_bkTyB hA, noRecIota_bkTyB hb⟩
  | _, _, _, .app _ _ _ _ _ hf ha => by
      simp only [bkTyB, NoRecIotaTy]
      exact ⟨noRecIota_bkTyB hf, noRecIota_bkTyB ha⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb => by
      simp only [bkTyB, NoRecIotaTy]
      exact ⟨noRecIota_bkTyB hA, noRecIota_bkTyB hv, noRecIota_bkTyB hb⟩
  | _, _, _, .lit _ _ _ hexp => by
      simp only [bkTyB, NoRecIotaTy]
      exact noRecIota_bkTyB hexp
  | _, _, _, .conv _ _ _ _ _ h hc => by
      simp only [bkTyB, NoRecIotaTy]
      exact ⟨noRecIota_bkTyB h, noRecIota_bkConvB hc⟩

/-- **Every back-translated twin conversion has ZERO ι steps at `R.f + 2`**
    (`w.recRef < R.f < R.f + 2` for every twin ι witness `w`). -/
theorem noRecIota_bkConvB :
    {Γ : LCtx} → {a b A : Expr Nat} → (c : ConvT R.twin₁ n Γ a b A) →
    NoRecIota (R.f + 2) (R.bkConvB c)
  | _, _, _, _, .refl _ _ _ h => by simp only [bkConvB, NoRecIota]; exact noRecIota_bkTyB h
  | _, _, _, _, .symm _ _ _ _ h => by simp only [bkConvB, NoRecIota]; exact noRecIota_bkConvB h
  | _, _, _, _, .trans _ _ _ _ _ h1 h2 => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB h1, noRecIota_bkConvB h2⟩
  | _, _, _, _, .beta _ _ _ _ _ _ hA hb ha => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkTyB hA, noRecIota_bkTyB hb, noRecIota_bkTyB ha⟩
  | _, _, _, _, .zeta _ _ _ _ _ _ hA hv hb => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkTyB hA, noRecIota_bkTyB hv, noRecIota_bkTyB hb⟩
  | _, _, _, _, .zetaLocal _ _ _ _ _ _ hv => by
      simp only [bkConvB, NoRecIota]
      exact noRecIota_bkTyB hv
  | _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ hb => by
      simp only [bkConvB, NoRecIota]
      exact noRecIota_bkTyB hb
  | _, _, _, _, .iota _ _ _ _ (.of w) hl hr => by
      simp only [bkConvB, bkIota, NoRecIota]
      have hlt : (R.bkWitness w).recRef < R.f := R.twin₁_rec_lt w
      exact ⟨by omega, noRecIota_bkTyB hl, noRecIota_bkTyB hr⟩
  | _, _, _, _, .lit _ _ _ _ _ hexp => by
      simp only [bkConvB, NoRecIota]
      exact noRecIota_bkTyB hexp
  | _, _, _, _, .app _ _ _ _ _ _ _ h1 h2 => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB h1, noRecIota_bkConvB h2⟩
  | _, _, _, _, .lam _ _ _ _ _ _ _ hA hb => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB hA, noRecIota_bkConvB hb⟩
  | _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB hA, noRecIota_bkConvB hB⟩
  | _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB hA, noRecIota_bkConvB hv, noRecIota_bkConvB hb⟩
  | _, _, _, _, .sorts _ _ _ _ => by simp only [bkConvB, NoRecIota]
  | _, _, _, _, .consts Γ r ls ls' m hres hlen hwf hwf' h => by
      simp only [bkConvB]
      exact R.noRecIota_bkConstsB Γ r ls ls' m hres hlen hwf hwf' h
  | _, _, _, _, .eta _ _ _ _ h => by simp only [bkConvB, NoRecIota]; exact noRecIota_bkTyB h
  | _, _, _, _, .irr _ _ _ _ hP hp hq => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkTyB hP, noRecIota_bkTyB hp, noRecIota_bkTyB hq⟩
  | _, _, _, _, .tyConv _ _ _ _ _ _ h hA => by
      simp only [bkConvB, NoRecIota]
      exact ⟨noRecIota_bkConvB h, noRecIota_bkConvB hA⟩
end

end BackB

/-! ## §2 Explicit-cast K-like cell `recTG_conv_recB` and round trip `trConv_selfB` -/

section RoundTripB

variable {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

/-- Weaken a closed typing `HasTyT E n [] e A` (`lift 0 1 e = e`, `lift 0 1 A = A`) to any `Γ`
    using explicit `castHT` and `castHTE`. -/
def hasTyTWeakenClosedB {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    {e A : Expr Nat} (he : lift 0 1 e = e) (hA : lift 0 1 A = A)
    (h0 : HasTyT E n [] e A) : (Γ : LCtx) → HasTyT E n Γ e A
  | [] => h0
  | d :: Γ =>
      castHT hA (castHTE he (hasTyTWeaken d hcl (c := 0) (hasTyTWeakenClosedB hcl he hA h0 Γ)))

theorem hasTyTWeakenClosedB_sort {E : ResolvedEnv} {n : Nat} (hcl : EnvClosed E)
    (l : Level) (Γ' : LCtx) :
    hasTyTWeakenClosedB hcl rfl rfl (HasTyT.sort (E := E) (n := n) [] l) Γ' =
      HasTyT.sort Γ' l := by
  induction Γ' with
  | nil => rfl
  | cons d Γ ih =>
      unfold hasTyTWeakenClosedB
      rw [ih]
      rfl

/-- `I : Sort uI` in `E`, built with `hasTyTWeakenClosedB`. -/
def hIEB (n : Nat) (Γ : LCtx) : HasTyT R.E n Γ R.I (.sort R.uI) :=
  hasTyTWeakenClosedB (envClosed_of_envWfT R.hW) (R.hclI 0) rfl
    (hasTyT_levelMono (Nat.zero_le n) (hasTyTExt R.base_ext R.hI)) Γ

/-- `F : Π (i : I), Sort 0` built with `castHT`. -/
def famConstB (Γ : LCtx) : HasTyT R.E n Γ (.const R.f []) (.pi R.I (.sort .zero)) :=
  castHT (R.shapeE.famTy_inst []) (.const Γ R.f [] (revFamM R.I) R.hEf rfl rfl)

/-- `F a : Sort 0` built with `famConstB`. -/
def famTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) :
    HasTyT R.E n Γ (.app (.const R.f []) a) (.sort .zero) :=
  .app Γ (.const R.f []) a R.I (.sort .zero) (R.famConstB Γ) ha

/-- `mk : Π (x : I), F x` built with `castHT`. -/
def mkConstB (Γ : LCtx) : HasTyT R.E n Γ (.const (R.f + 1) []) (.pi R.I (famApp0 R.f)) :=
  castHT (R.shapeE.ctorTy_inst []) (.const Γ (R.f + 1) [] (revCtorM R.f R.I) R.hEf1 rfl rfl)

/-- `mk a : F a` built with `mkConstB`. -/
def mkTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) :
    HasTyT R.E n Γ (.app (.const (R.f + 1) []) a) (.app (.const R.f []) a) :=
  .app Γ (.const (R.f + 1) []) a R.I (famApp0 R.f) (R.mkConstB Γ) ha

/-- `motTy l` typed using `hIEB` and `famTyB`. -/
def motTyTB (Γ : LCtx) (l : Level) :
    HasTyT R.E n Γ (motTy R.f R.I l) (.sort (.imax R.uI (.imax .zero (.succ l)))) :=
  .pi Γ R.I R.uI (.pi (famApp0 R.f) (.sort l)) (.imax .zero (.succ l)) (R.hIEB n Γ)
    (.pi _ (famApp0 R.f) .zero (.sort l) (.succ l)
      (R.famTyB (.bvar _ 0 _ (by simp [lookupType, R.shapeE.liftI]))) (.sort _ l))

/-- `minTy` typed using `hIEB` and `mkTyB`. -/
def minTyTB (Γ : LCtx) (l : Level) :
    HasTyT R.E n (R.shapeE.g1 Γ l) (minTy R.f R.I) (.sort (.imax R.uI l)) :=
  .pi _ R.I R.uI _ l (R.hIEB n _)
    (.app _ _ _ (.app (.const R.f []) (.bvar 0)) (.sort l)
      (.app _ _ _ R.I (.pi (famApp0 R.f) (.sort l))
        (.bvar _ 1 (motTy R.f R.I l) (R.shapeE.lk_g1I_1 Γ l))
        (.bvar _ 0 _ (R.shapeE.lk_g1I_0 Γ l)))
      (R.mkTyB (.bvar _ 0 _ (R.shapeE.lk_g1I_0 Γ l))))

/-- `rec.{[l]}` typed using `castHT`. -/
def recConstLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n Γ (.const (R.f + 2) [l]) (recTyG R.f R.I l) :=
  castHT (R.shapeE.recTyS_inst l)
    (.const Γ (R.f + 2) [l] (revRecM R.f R.I) R.hEf2 rfl hl)

def rec1LB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 3))
      (.pi R.shapeE.minTy3 (.pi R.I (.pi (famApp0 R.f) (.app (.app (.bvar 6) (.bvar 1)) (.bvar 0))))) :=
  castHT (by simp [instantiate0, instantiate, lift, minTy, RevShape.minTy3, instantiate_of_closed R.I (R.hclI 0)])
    (.app (R.shapeE.g4 Γ l) _ (.bvar 3) _ _ (R.recConstLB _ l hl)
      (.bvar _ 3 (motTy R.f R.I l) (R.shapeE.lk_g4_3 Γ l)))

def rec2LB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 3)) (.bvar 2))
      (.pi R.I (.pi (famApp0 R.f) (.app (.app (.bvar 5) (.bvar 1)) (.bvar 0)))) :=
  castHT (by simp [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)])
    (.app (R.shapeE.g4 Γ l) _ (.bvar 2) _ _ (R.rec1LB Γ l hl)
      (.bvar _ 2 R.shapeE.minTy3 (R.shapeE.lk_g4_2 Γ l)))

def rec3LB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1])
      (.pi (.app (.const R.f []) (.bvar 1)) (.app (.app (.bvar 4) (.bvar 2)) (.bvar 0))) :=
  castHT (by simp [instantiate0, instantiate, lift, foldApps])
    (.app (R.shapeE.g4 Γ l) _ (.bvar 1) _ _ (R.rec2LB Γ l hl)
      (.bvar _ 1 R.I (R.shapeE.lk_g4_1 Γ l)))

/-- The K-like cell built with `iotaOfWitness` and `castHT` (no tactic-block `rw`/`simpa`). -/
def kcellLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n (R.shapeE.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
  let S := R.shapeE
  let hX : HasTyT R.E n (S.g4 Γ l) (.bvar 1) R.I := .bvar _ 1 _ (S.lk_g4_1 Γ l)
  let hRI : HasTyT R.E n (S.g4 Γ l) (.app (.const R.f []) (.bvar 1)) (.sort .zero) := R.famTyB hX
  let hh : HasTyT R.E n (S.g4 Γ l) (.bvar 0) (.app (.const R.f []) (.bvar 1)) := .bvar _ 0 _ (S.lk_g4_0 Γ l)
  let hmk : HasTyT R.E n (S.g4 Γ l) (.app (.const (R.f + 1) []) (.bvar 1)) (.app (.const R.f []) (.bvar 1)) :=
    R.mkTyB hX
  let cIrr : ConvT R.E n (S.g4 Γ l) (.bvar 0) (.app (.const (R.f + 1) []) (.bvar 1))
      (.app (.const R.f []) (.bvar 1)) :=
    .irr _ _ _ _ hRI hh hmk
  let h3 := R.rec3LB Γ l hl
  let hMid : HasTyT R.E n (S.g4 Γ l)
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    HasTyT.app (S.g4 Γ l) _ (.app (.const (R.f + 1) []) (.bvar 1)) _ _ h3 hmk
  let hRhs : HasTyT R.E n (S.g4 Γ l) (.app (.bvar 2) (.bvar 1))
      (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    HasTyT.app (S.g4 Γ l) (.bvar 2) (.bvar 1) _ _ (.bvar _ 2 S.minTy3 (S.lk_g4_2 Γ l)) hX
  let hMX : HasTyT R.E n (S.g4 Γ l) (.app (.bvar 3) (.bvar 1))
      (.pi (.app (.const R.f []) (.bvar 1)) (.sort l)) :=
    HasTyT.app (S.g4 Γ l) (.bvar 3) (.bvar 1) _ _ (.bvar _ 3 (motTy R.f R.I l) (S.lk_g4_3 Γ l)) hX
  let step1 : ConvT R.E n (S.g4 Γ l) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) :=
    .app _ _ _ (.bvar 0) (.app (.const (R.f + 1) []) (.bvar 1)) _ _ (.refl _ _ _ h3) cIrr
  let cIota : ConvT R.E n (S.g4 Γ l)
      (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .app (.const (R.f + 1) []) (.bvar 1)])
      (.app (.bvar 2) (.bvar 1)) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1))) :=
    iotaOfWitness (R.revWAt l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1))
      (R.revWAt_lhs l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1))
      (R.revWAt_rhs l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)) hMid hRhs
  let tyFix : ConvT R.E n (S.g4 Γ l) (.app (.app (.bvar 3) (.bvar 1)) (.app (.const (R.f + 1) []) (.bvar 1)))
      (.app (.app (.bvar 3) (.bvar 1)) (.bvar 0)) (.sort l) :=
    .app _ _ _ (.app (.const (R.f + 1) []) (.bvar 1)) (.bvar 0) _ _ (.refl _ _ _ hMX) (.symm _ _ _ _ cIrr)
  .trans _ _ _ _ _ step1 (.tyConv _ _ _ _ _ l cIota tyFix)

def recEta1B (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g1 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 0)) R.shapeE.recTy1 :=
  castHT (by simp [instantiate0, instantiate, lift, minTy, RevShape.recTy1, instantiate_of_closed R.I (R.hclI 0)])
    (.app (R.shapeE.g1 Γ l) _ (.bvar 0) _ _ (R.recConstLB _ l hl)
      (.bvar _ 0 (motTy R.f R.I l) (by simp [lookupType, RevShape.g1, R.shapeE.lift_motTy])))

def recEta2B (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g2 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 1)) (.bvar 0))
      (.pi R.I (.pi (famApp0 R.f) recB4)) :=
  let h1 := HasTyT.app (R.shapeE.g2 Γ l) _ (.bvar 1) _ _ (R.recConstLB _ l hl)
    (.bvar _ 1 (motTy R.f R.I l) (by simp [lookupType, RevShape.g2, RevShape.g1, R.shapeE.lift_motTy]))
  let h2 := HasTyT.app (R.shapeE.g2 Γ l) _ (.bvar 0) _ _ h1
    (.bvar _ 0 (instantiate 0 (.bvar 1) (minTy R.f R.I))
      (by simp [lookupType, RevShape.g2, minTy, lift, instantiate, R.liftI, instantiate_of_closed R.I (R.hclI 0)]))
  castHT (by simp [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)]) h2

def recEta3B (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    HasTyT R.E n (R.shapeE.g3 Γ l) (.app (.app (.app (.const (R.f + 2) [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.pi (famApp0 R.f) recB4) :=
  let h1 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 2) _ _ (R.recConstLB _ l hl)
    (.bvar _ 2 (motTy R.f R.I l)
      (by simp [lookupType, RevShape.g3, RevShape.g2, RevShape.g1, R.shapeE.lift_motTy]))
  let h2 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 1) _ _ h1
    (.bvar _ 1 (instantiate 0 (.bvar 2) (minTy R.f R.I))
      (by simp [lookupType, RevShape.g3, RevShape.g2, minTy, lift, instantiate, R.liftI,
        instantiate_of_closed R.I (R.hclI 0)]))
  let h3 := HasTyT.app (R.shapeE.g3 Γ l) _ (.bvar 0) _ _ h2
    (.bvar _ 0 (instantiate 0 (Expr.bvar 1) (instantiate (0 + 1) (lift 0 1 (Expr.bvar 2)) R.I))
      (by simp [lookupType, RevShape.g3, R.liftI, instantiate_of_closed R.I (R.hclI 0)]))
  castHT (by simp [instantiate0, instantiate, lift, instantiate_of_closed R.I (R.hclI 0)]) h3

def recE_conv_recTGB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (R.recE l) (recTG R.f R.I l) (recTyG R.f R.I l) :=
  let S := R.shapeE
  .lam Γ (motTy R.f R.I l) (motTy R.f R.I l) _ _ _ _ (.refl _ _ _ (R.motTyTB Γ l))
    (.lam _ (minTy R.f R.I) (minTy R.f R.I) _ _ _ _ (.refl _ _ _ (R.minTyTB Γ l))
      (.lam _ R.I R.I _ _ _ R.uI (.refl _ _ _ (R.hIEB n _))
        (.lam _ (famApp0 R.f) (famApp0 R.f) _ _ recB4 .zero
          (.refl _ _ _ (R.famTyB (.bvar _ 0 _ (S.lk_g3_0 Γ l)))) (R.kcellLB Γ l hl))))

def rec_conv_recEB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (.const (R.f + 2) [l]) (R.recE l) (recTyG R.f R.I l) :=
  let S := R.shapeE
  let h0 := R.recConstLB Γ l hl
  let h1 := R.recEta1B Γ l hl
  let h2 := R.recEta2B Γ l hl
  let h3 := R.recEta3B Γ l hl
  let e4 : ConvT R.E n (S.g3 Γ l) (.app (.app (.app (.const (R.f + 2) [l]) (.bvar 2)) (.bvar 1)) (.bvar 0))
      (.lam (famApp0 R.f) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0]))
      (.pi (famApp0 R.f) recB4) :=
    .symm _ _ _ _ (.eta (S.g3 Γ l) _ _ _ h3)
  let e3 : ConvT R.E n (S.g2 Γ l) (.app (.app (.const (R.f + 2) [l]) (.bvar 1)) (.bvar 0))
      (.lam R.I (.lam (famApp0 R.f) (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))
      (.pi R.I (.pi (famApp0 R.f) recB4)) :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta (S.g2 Γ l) _ _ _ h2))
      (.lam (S.g2 Γ l) R.I R.I _ _ _ R.uI (.refl _ _ _ (R.hIEB n _)) e4)
  let e2 : ConvT R.E n (S.g1 Γ l) (.app (.const (R.f + 2) [l]) (.bvar 0))
      (.lam (minTy R.f R.I) (.lam R.I (.lam (famApp0 R.f)
        (foldApps (.const (R.f + 2) [l]) [.bvar 3, .bvar 2, .bvar 1, .bvar 0])))) S.recTy1 :=
    .trans _ _ _ _ _ (.symm _ _ _ _ (.eta (S.g1 Γ l) _ _ _ h1))
      (.lam (S.g1 Γ l) (minTy R.f R.I) (minTy R.f R.I) _ _ _ _ (.refl _ _ _ (R.minTyTB Γ l)) e3)
  .trans _ _ _ _ _ (.symm _ _ _ _ (.eta Γ _ _ _ h0))
    (.lam Γ (motTy R.f R.I l) (motTy R.f R.I l) _ _ _ _ (.refl _ _ _ (R.motTyTB Γ l)) e2)

/-- **`recTG l ≡ rec.{l}` rebuilt with explicit `castHT` and `iotaOfWitness`.** -/
def recTG_conv_recB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    ConvT R.E n Γ (recTG R.f R.I l) (.const (R.f + 2) [l]) (recTyG R.f R.I l) :=
  .symm _ _ _ _ (.trans _ _ _ _ _ (R.rec_conv_recEB Γ l hl) (R.recE_conv_recTGB Γ l hl))

/-- Constant leaf of `trConv_selfB`, using `castCL`, `castCR`, and `castT`. -/
def trConv_constB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.E.members r = some m) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true) :
    ConvT R.E n Γ (.const r ls) (tr R.f R.I (.const r ls)) (instantiateLevels ls m.mtype) :=
  if h2 : r = R.f + 2 then
    match ls, hlen, hwf with
    | [l], _, hwf1 =>
      have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      have hlhs : Expr.const (R.f + 2) [l] = Expr.const r [l] := congrArg (fun k => Expr.const k [l]) h2.symm
      have he : tr R.f R.I (.const r [l]) = recTG R.f R.I l := by rw [h2, tr_rec]
      have hT : recTyG R.f R.I l = instantiateLevels [l] m.mtype := by
        rw [hm]; exact (R.shapeE.recTyS_inst l).symm
      castCL hlhs (castCR he.symm (castT hT (.symm _ _ _ _ (R.recTG_conv_recB Γ l hwf1))))
    | [], hlen0, _ => by
      have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen0
      exact Nat.noConfusion hlen0
    | _ :: _ :: _, hlen2, _ => by
      have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen2
      exact Nat.noConfusion (Nat.succ.inj hlen2)
  else
    castCR (tr_const_ne R.f R.I h2 ls).symm (.refl _ _ _ (.const Γ r ls m hres hlen hwf))

/-- `Type`-valued round-trip conversion `e ≡ tr R.f R.I e : A` in `R.E`. -/
def trConv_selfB : {Γ : LCtx} → {e A : Expr Nat} → HasTyT R.E n Γ e A →
    ConvT R.E n Γ e (tr R.f R.I e) A
  | _, _, _, .sort Γ l => .refl _ _ _ (.sort Γ l)
  | _, _, _, .bvar Γ i A h => .refl _ _ _ (.bvar Γ i A h)
  | _, _, _, .const Γ r ls m hres hlen hwf => R.trConv_constB Γ r ls m hres hlen hwf
  | _, _, _, .pi Γ A u B v hA hB =>
      .pi Γ A (tr R.f R.I A) B (tr R.f R.I B) u v (trConv_selfB hA) (trConv_selfB hB)
  | _, _, _, .lam Γ A u body B hA hbody =>
      .lam Γ A (tr R.f R.I A) body (tr R.f R.I body) B u (trConv_selfB hA) (trConv_selfB hbody)
  | _, _, _, .app Γ g a A B hf ha =>
      .app Γ g (tr R.f R.I g) a (tr R.f R.I a) A B (trConv_selfB hf) (trConv_selfB ha)
  | _, _, _, .letE Γ A u value B body hA hv hb =>
      .letE Γ A (tr R.f R.I A) value (tr R.f R.I value) body (tr R.f R.I body) B u
        (trConv_selfB hA) (trConv_selfB hv) (trConv_selfB hb)
  | _, _, _, .lit Γ t T hexp => .refl _ _ _ (.lit Γ t T hexp)
  | _, _, _, .conv Γ e A B u h hc =>
      .tyConv Γ e (tr R.f R.I e) A B u (trConv_selfB h) hc

theorem lok_famConstB (Γ : LCtx) : LOKt σ N K (R.famConstB (n := n) Γ) := by
  simp only [famConstB, LOKt_castHT, LOKt, levelsOK_nil]

theorem lok_famTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) (h : LOKt σ N K ha) :
    LOKt σ N K (R.famTyB ha) := by
  simp only [famTyB, LOKt]
  exact ⟨R.lok_famConstB Γ, h⟩

theorem lok_mkConstB (Γ : LCtx) : LOKt σ N K (R.mkConstB (n := n) Γ) := by
  simp only [mkConstB, LOKt_castHT, LOKt, levelsOK_nil]

theorem lok_mkTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) (h : LOKt σ N K ha) :
    LOKt σ N K (R.mkTyB ha) := by
  simp only [mkTyB, LOKt]
  exact ⟨R.lok_mkConstB Γ, h⟩

theorem lok_motTyTB (Γ : LCtx) (l : Level) (_h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N)
    (hlN : evalTotal σ l + 1 ≤ N) (hI : LOKt σ N K (R.hIEB n Γ)) :
    LOKt σ N K (R.motTyTB (n := n) Γ l) := by
  have hz : evalTotal σ .zero ≤ N := Nat.zero_le N
  have him : evalTotal σ (.imax .zero (.succ l)) ≤ N := by
    simp [evalTotal, Nat.max_le, hlN]
  have hfam : LOKt σ N K (R.famTyB
    (HasTyT.bvar (n := n) (.assumption R.I :: Γ) 0 R.I (by simp [lookupType, R.shapeE.liftI]))) :=
    R.lok_famTyB _ trivial
  simp only [motTyTB, LOKt]
  exact ⟨huIN, him, hI, hz, hlN, hfam, hlN⟩

theorem lok_minTyTB (Γ : LCtx) (l : Level) (huIN : evalTotal σ R.uI ≤ N)
    (hl0 : evalTotal σ l ≤ N) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKt σ N K (R.minTyTB (n := n) Γ l) := by
  have hmk : LOKt σ N K (R.mkTyB
    (HasTyT.bvar (n := n) (.assumption R.I :: R.shapeE.g1 Γ l) 0 R.I (R.shapeE.lk_g1I_0 Γ l))) :=
    R.lok_mkTyB _ trivial
  simp only [minTyTB, LOKt]
  exact ⟨huIN, hl0, hI _, ⟨trivial, trivial⟩, hmk⟩

theorem lok_recConstLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true)
    (hK : LevelsOK σ (K (R.f + 2)) [l]) :
    LOKt σ N K (R.recConstLB Γ l hl) := by
  simp only [recConstLB, LOKt_castHT, LOKt]
  exact hK

theorem lok_rec3LB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true)
    (hK : LevelsOK σ (K (R.f + 2)) [l]) :
    LOKt σ N K (R.rec3LB Γ l hl) := by
  simp only [rec3LB, rec2LB, rec1LB, LOKt_castHT, LOKt]
  exact ⟨⟨⟨R.lok_recConstLB _ l hl hK, trivial⟩, trivial⟩, trivial⟩

theorem lok_kcellLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true)
    (hK : LevelsOK σ (K (R.f + 2)) [l]) :
    LOKc σ N K (R.kcellLB Γ l hl) := by
  have hRI : LOKt σ N K (R.famTyB
    (HasTyT.bvar (n := n) (R.shapeE.g4 Γ l) 1 R.I (R.shapeE.lk_g4_1 Γ l))) :=
    R.lok_famTyB _ trivial
  have hmk : LOKt σ N K (R.mkTyB
    (HasTyT.bvar (n := n) (R.shapeE.g4 Γ l) 1 R.I (R.shapeE.lk_g4_1 Γ l))) :=
    R.lok_mkTyB _ trivial
  have h3 : LOKt σ N K (R.rec3LB Γ l hl) := R.lok_rec3LB Γ l hl hK
  simp only [kcellLB, LOKc, LOKt, lok_iotaOfWitness]
  exact ⟨⟨h3, hRI, trivial, hmk⟩, ⟨⟨h3, hmk⟩, trivial, trivial⟩, ⟨trivial, trivial⟩, hRI, trivial, hmk⟩

theorem lok_recTG_conv_recB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true)
    (h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N) (hlN : evalTotal σ l + 1 ≤ N)
    (hK : LevelsOK σ (K (R.f + 2)) [l])
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKc σ N K (R.recTG_conv_recB Γ l hl) := by
  have hl0 : evalTotal σ l ≤ N := Nat.le_of_succ_le hlN
  have hmot := R.lok_motTyTB Γ l h1N huIN hlN (hI Γ)
  have hmin := R.lok_minTyTB Γ l huIN hl0 hI
  have hfam : LOKt σ N K (R.famTyB
    (HasTyT.bvar (n := n) (R.shapeE.g3 Γ l) 0 R.I (R.shapeE.lk_g3_0 Γ l))) :=
    R.lok_famTyB _ trivial
  have hrc : LOKt σ N K (R.recConstLB Γ l hl) := R.lok_recConstLB Γ l hl hK
  have heta1 : LOKt σ N K (R.recEta1B Γ l hl) := by
    simp only [recEta1B, LOKt_castHT, LOKt]
    exact ⟨R.lok_recConstLB _ l hl hK, trivial⟩
  have heta2 : LOKt σ N K (R.recEta2B Γ l hl) := by
    simp only [recEta2B, LOKt_castHT, LOKt]
    exact ⟨⟨R.lok_recConstLB _ l hl hK, trivial⟩, trivial⟩
  have heta3 : LOKt σ N K (R.recEta3B Γ l hl) := by
    simp only [recEta3B, LOKt_castHT, LOKt]
    exact ⟨⟨⟨R.lok_recConstLB _ l hl hK, trivial⟩, trivial⟩, trivial⟩
  have hk : LOKc σ N K (R.kcellLB Γ l hl) := R.lok_kcellLB Γ l hl hK
  simp only [recTG_conv_recB, rec_conv_recEB, recE_conv_recTGB, LOKc]
  exact ⟨⟨hrc, hmot, heta1, hmin, heta2, hI _, heta3⟩, hmot, hmin, hI _, hfam, hk⟩

theorem lok_trConv_constB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N) (hKN : K (R.f + 2) + 1 ≤ N)
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (hd : LevelsOK σ (K r) ls) :
    LOKc σ N K (R.trConv_constB Γ r ls m hres hlen hwf) := by
  unfold trConv_constB
  split
  · next h2 =>
    rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen
      exact Nat.noConfusion hlen
    · simp only [LOKc_castCL, LOKc_castCR, LOKc_castT, LOKc]
      have hK : LevelsOK σ (K (R.f + 2)) [l] := by rw [← h2]; exact hd
      have hlK : evalTotal σ l ≤ K (R.f + 2) := hK l (List.Mem.head [])
      have hlN : evalTotal σ l + 1 ≤ N := by omega
      exact R.lok_recTG_conv_recB Γ l hwf h1N huIN hlN hK hI
    · have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen
      exact Nat.noConfusion (Nat.succ.inj hlen)
  · simp only [LOKc_castCR, LOKc, LOKt]
    exact hd

/-- **`trConv_selfB` preserves `LOK`**: if `d : HasTyT R.E n Γ e A` satisfies `LOKt σ N K d`,
    then `R.trConv_selfB d` satisfies `LOKc σ N K` whenever `1 ≤ N`, `evalTotal σ R.uI ≤ N`,
    `K (R.f + 2) + 1 ≤ N`, and `R.hIEB` is bounded. -/
theorem lok_trConv_selfB (h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N)
    (hKN : K (R.f + 2) + 1 ≤ N) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT R.E n Γ e A) →
    LOKt σ N K d → LOKc σ N K (R.trConv_selfB d)
  | _, _, _, .sort _ _, hd => by simp only [trConv_selfB, LOKc]; exact hd
  | _, _, _, .bvar _ _ _ _, hd => by simp only [trConv_selfB, LOKc]; exact hd
  | _, _, _, .const Γ r ls m hres hlen hwf, hd => by
      simp only [trConv_selfB]
      exact R.lok_trConv_constB Γ r ls m hres hlen hwf h1N huIN hKN hI hd
  | _, _, _, .pi _ _ _ _ _ hA hB, hd => by
      simp only [trConv_selfB, LOKc]
      exact ⟨hd.1, hd.2.1, lok_trConv_selfB h1N huIN hKN hI hA hd.2.2.1,
        lok_trConv_selfB h1N huIN hKN hI hB hd.2.2.2⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, hd => by
      simp only [trConv_selfB, LOKc]
      exact ⟨lok_trConv_selfB h1N huIN hKN hI hA hd.1,
        lok_trConv_selfB h1N huIN hKN hI hb hd.2⟩
  | _, _, _, .app _ _ _ _ _ hf ha, hd => by
      simp only [trConv_selfB, LOKc]
      exact ⟨lok_trConv_selfB h1N huIN hKN hI hf hd.1,
        lok_trConv_selfB h1N huIN hKN hI ha hd.2⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hd => by
      simp only [trConv_selfB, LOKc]
      exact ⟨lok_trConv_selfB h1N huIN hKN hI hA hd.1,
        lok_trConv_selfB h1N huIN hKN hI hv hd.2.1,
        lok_trConv_selfB h1N huIN hKN hI hb hd.2.2⟩
  | _, _, _, .lit _ _ _ hexp, hd => by simp only [trConv_selfB, LOKc]; exact hd
  | _, _, _, .conv _ _ _ _ _ h hc, hd => by
      simp only [trConv_selfB, LOKc]
      exact ⟨lok_trConv_selfB h1N huIN hKN hI h hd.1, hd.2⟩

/-- The K-cell's ι witness `R.revWAt l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)` is diagonal
    (`field = index = .bvar 1`). -/
theorem diagWitness_kcell (l : Level) :
    DiagWitnessAt (R.f + 2) (R.revWAt l [] (.bvar 3) (.bvar 2) (.bvar 1) (.bvar 1)) :=
  fun _ => ⟨.bvar 3, .bvar 2, .bvar 1, rfl, rfl⟩

theorem diagRecIotaTy_famConstB (Γ : LCtx) :
    DiagRecIotaTy (R.f + 2) (R.famConstB (n := n) Γ) := by
  simp only [famConstB, diagRecIotaTy_castHT, DiagRecIotaTy]

theorem diagRecIotaTy_famTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (h : DiagRecIotaTy (R.f + 2) ha) :
    DiagRecIotaTy (R.f + 2) (R.famTyB ha) := by
  simp only [famTyB, DiagRecIotaTy]
  exact ⟨R.diagRecIotaTy_famConstB Γ, h⟩

theorem diagRecIotaTy_mkConstB (Γ : LCtx) :
    DiagRecIotaTy (R.f + 2) (R.mkConstB (n := n) Γ) := by
  simp only [mkConstB, diagRecIotaTy_castHT, DiagRecIotaTy]

theorem diagRecIotaTy_mkTyB {Γ : LCtx} {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (h : DiagRecIotaTy (R.f + 2) ha) :
    DiagRecIotaTy (R.f + 2) (R.mkTyB ha) := by
  simp only [mkTyB, DiagRecIotaTy]
  exact ⟨R.diagRecIotaTy_mkConstB Γ, h⟩

theorem diagRecIotaTy_motTyTB (Γ : LCtx) (l : Level)
    (hI : DiagRecIotaTy (R.f + 2) (R.hIEB n Γ)) :
    DiagRecIotaTy (R.f + 2) (R.motTyTB (n := n) Γ l) := by
  have hfam := R.diagRecIotaTy_famTyB
    (HasTyT.bvar (n := n) (.assumption R.I :: Γ) 0 R.I (by simp [lookupType, R.shapeE.liftI]))
    (diagRecIotaTy_bvar _ _)
  simp only [motTyTB, DiagRecIotaTy]
  exact ⟨hI, hfam, trivial⟩

theorem diagRecIotaTy_minTyTB (Γ : LCtx) (l : Level)
    (hI : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ')) :
    DiagRecIotaTy (R.f + 2) (R.minTyTB (n := n) Γ l) := by
  have hmk := R.diagRecIotaTy_mkTyB
    (HasTyT.bvar (n := n) (.assumption R.I :: R.shapeE.g1 Γ l) 0 R.I (R.shapeE.lk_g1I_0 Γ l))
    (diagRecIotaTy_bvar _ _)
  simp only [minTyTB, DiagRecIotaTy]
  exact ⟨hI _, ⟨trivial, trivial⟩, hmk⟩

theorem diagRecIotaTy_recConstLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    DiagRecIotaTy (R.f + 2) (R.recConstLB Γ l hl) := by
  simp only [recConstLB, diagRecIotaTy_castHT, DiagRecIotaTy]

theorem diagRecIotaTy_rec3LB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    DiagRecIotaTy (R.f + 2) (R.rec3LB Γ l hl) := by
  simp only [rec3LB, rec2LB, rec1LB, diagRecIotaTy_castHT, DiagRecIotaTy]
  exact ⟨⟨⟨R.diagRecIotaTy_recConstLB _ l hl, trivial⟩, trivial⟩, trivial⟩

theorem diagRecIota_kcellLB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true) :
    DiagRecIota (R.f + 2) (R.kcellLB Γ l hl) := by
  have hRI := R.diagRecIotaTy_famTyB
    (HasTyT.bvar (n := n) (R.shapeE.g4 Γ l) 1 R.I (R.shapeE.lk_g4_1 Γ l)) (diagRecIotaTy_bvar _ _)
  have hmk := R.diagRecIotaTy_mkTyB
    (HasTyT.bvar (n := n) (R.shapeE.g4 Γ l) 1 R.I (R.shapeE.lk_g4_1 Γ l)) (diagRecIotaTy_bvar _ _)
  have h3 := R.diagRecIotaTy_rec3LB Γ l hl
  simp only [kcellLB, DiagRecIota, DiagRecIotaTy, diagRecIota_iotaOfWitness]
  exact ⟨⟨h3, hRI, trivial, hmk⟩,
    ⟨R.diagWitness_kcell l, ⟨h3, hmk⟩, trivial, trivial⟩,
    ⟨trivial, trivial⟩, hRI, trivial, hmk⟩

/-- **The K-like cell `recTG_conv_recB` uses ONLY diagonal ι steps at `R.f + 2`.** -/
theorem diagRecIota_recTG_conv_recB (Γ : LCtx) (l : Level) (hl : levelsBounded n [l] = true)
    (hI : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ')) :
    DiagRecIota (R.f + 2) (R.recTG_conv_recB Γ l hl) := by
  have hmot := R.diagRecIotaTy_motTyTB Γ l (hI Γ)
  have hmin := R.diagRecIotaTy_minTyTB Γ l hI
  have hfam := R.diagRecIotaTy_famTyB
    (HasTyT.bvar (n := n) (R.shapeE.g3 Γ l) 0 R.I (R.shapeE.lk_g3_0 Γ l)) (diagRecIotaTy_bvar _ _)
  have hrc := R.diagRecIotaTy_recConstLB Γ l hl
  have heta1 : DiagRecIotaTy (R.f + 2) (R.recEta1B Γ l hl) := by
    simp only [recEta1B, diagRecIotaTy_castHT, DiagRecIotaTy]
    exact ⟨R.diagRecIotaTy_recConstLB _ l hl, trivial⟩
  have heta2 : DiagRecIotaTy (R.f + 2) (R.recEta2B Γ l hl) := by
    simp only [recEta2B, diagRecIotaTy_castHT, DiagRecIotaTy]
    exact ⟨⟨R.diagRecIotaTy_recConstLB _ l hl, trivial⟩, trivial⟩
  have heta3 : DiagRecIotaTy (R.f + 2) (R.recEta3B Γ l hl) := by
    simp only [recEta3B, diagRecIotaTy_castHT, DiagRecIotaTy]
    exact ⟨⟨⟨R.diagRecIotaTy_recConstLB _ l hl, trivial⟩, trivial⟩, trivial⟩
  have hk := R.diagRecIota_kcellLB Γ l hl
  simp only [recTG_conv_recB, rec_conv_recEB, recE_conv_recTGB, DiagRecIota]
  exact ⟨⟨hrc, hmot, heta1, hmin, heta2, hI _, heta3⟩, hmot, hmin, hI _, hfam, hk⟩

theorem diagRecIota_trConv_constB (Γ : LCtx) (r : Nat) (ls : List Level) (m : CheckedMember)
    (hres : R.E.members r = some m) (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (hI : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ')) :
    DiagRecIota (R.f + 2) (R.trConv_constB Γ r ls m hres hlen hwf) := by
  unfold trConv_constB
  split
  · next h2 =>
    rcases ls with _ | ⟨l, _ | ⟨l', ls⟩⟩
    · have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen
      exact Nat.noConfusion hlen
    · simp only [diagRecIota_castCL, diagRecIota_castCR, diagRecIota_castT, DiagRecIota]
      exact R.diagRecIota_recTG_conv_recB Γ l hwf hI
    · have hm : m = revRecM R.f R.I := by rw [h2, R.hEf2] at hres; exact (Option.some.inj hres).symm
      rw [hm] at hlen
      exact Nat.noConfusion (Nat.succ.inj hlen)
  · simp only [diagRecIota_castCR, DiagRecIota, DiagRecIotaTy]

/-- **The round trip `trConv_selfB` preserves `DiagRecIota (R.f + 2)`** (every `.iota` at `R.f + 2`
    introduced by `trConv_selfB` is the diagonal witness `field = index = .bvar 1`). -/
theorem diagRecIota_trConv_selfB
    (hI : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ')) :
    {Γ : LCtx} → {e A : Expr Nat} → (d : HasTyT R.E n Γ e A) →
    DiagRecIotaTy (R.f + 2) d → DiagRecIota (R.f + 2) (R.trConv_selfB d)
  | _, _, _, .sort _ _, hd => by simp only [trConv_selfB, DiagRecIota]; exact hd
  | _, _, _, .bvar _ _ _ _, hd => by simp only [trConv_selfB, DiagRecIota]; exact hd
  | _, _, _, .const Γ r ls m hres hlen hwf, _ => by
      simp only [trConv_selfB]
      exact R.diagRecIota_trConv_constB Γ r ls m hres hlen hwf hI
  | _, _, _, .pi _ _ _ _ _ hA hB, hd => by
      simp only [trConv_selfB, DiagRecIota]
      exact ⟨diagRecIota_trConv_selfB hI hA hd.1, diagRecIota_trConv_selfB hI hB hd.2⟩
  | _, _, _, .lam _ _ _ _ _ hA hb, hd => by
      simp only [trConv_selfB, DiagRecIota]
      exact ⟨diagRecIota_trConv_selfB hI hA hd.1, diagRecIota_trConv_selfB hI hb hd.2⟩
  | _, _, _, .app _ _ _ _ _ hf ha, hd => by
      simp only [trConv_selfB, DiagRecIota]
      exact ⟨diagRecIota_trConv_selfB hI hf hd.1, diagRecIota_trConv_selfB hI ha hd.2⟩
  | _, _, _, .letE _ _ _ _ _ _ hA hv hb, hd => by
      simp only [trConv_selfB, DiagRecIota]
      exact ⟨diagRecIota_trConv_selfB hI hA hd.1, diagRecIota_trConv_selfB hI hv hd.2.1,
        diagRecIota_trConv_selfB hI hb hd.2.2⟩
  | _, _, _, .lit _ _ _ hexp, hd => by simp only [trConv_selfB, DiagRecIota]; exact hd
  | _, _, _, .conv _ _ _ _ _ h hc, hd => by
      simp only [trConv_selfB, DiagRecIota]
      exact ⟨diagRecIota_trConv_selfB hI h hd.1, hd.2⟩

/-- **Combined twin-round-trip index conversion** in a context fixed by `trCtx R.f R.I`:
    any conversion `cT : ConvT R.twin₁ n Γ (tr R.f R.I x) (tr R.f R.I x') R.I` in the twin
    combines with `trConv_selfB hx` and `trConv_selfB hx'` to give `ConvT R.E n Γ x x' R.I`
    with ONLY diagonal ι steps at `R.f + 2` and preserving `LOKc σ N K`. -/
def twinIdxConvB {Γ : LCtx} {x x' : Expr Nat}
    (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (cT : ConvT R.twin₁ n Γ (tr R.f R.I x) (tr R.f R.I x') R.I) :
    ConvT R.E n Γ x x' R.I :=
  .trans Γ x (tr R.f R.I x) x' R.I (R.trConv_selfB hx)
    (.trans Γ (tr R.f R.I x) (tr R.f R.I x') x' R.I (R.bkConvB cT)
      (.symm Γ x' (tr R.f R.I x') R.I (R.trConv_selfB hx')))

theorem twinIdxConvB_lok_and_diag
    {Γ : LCtx} {x x' : Expr Nat}
    (hx : HasTyT R.E n Γ x R.I) (hx' : HasTyT R.E n Γ x' R.I)
    (cT : ConvT R.twin₁ n Γ (tr R.f R.I x) (tr R.f R.I x') R.I)
    (h1N : 1 ≤ N) (huIN : evalTotal σ R.uI ≤ N) (hKN : K (R.f + 2) + 1 ≤ N)
    (hI_lok : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (hI_diag : ∀ Γ', DiagRecIotaTy (R.f + 2) (R.hIEB n Γ'))
    (hlok_x : LOKt σ N K hx) (hlok_x' : LOKt σ N K hx') (hlok_cT : LOKc σ N K cT)
    (hdiag_x : DiagRecIotaTy (R.f + 2) hx) (hdiag_x' : DiagRecIotaTy (R.f + 2) hx') :
    LOKc σ N K (R.twinIdxConvB hx hx' cT) ∧ DiagRecIota (R.f + 2) (R.twinIdxConvB hx hx' cT) :=
  ⟨⟨R.lok_trConv_selfB h1N huIN hKN hI_lok hx hlok_x,
      (R.lok_bkConvB cT).mpr hlok_cT,
      R.lok_trConv_selfB h1N huIN hKN hI_lok hx' hlok_x'⟩,
    ⟨R.diagRecIota_trConv_selfB hI_diag hx hdiag_x,
      diagRecIota_of_noRecIota (R.bkConvB cT) (R.noRecIota_bkConvB cT),
      R.diagRecIota_trConv_selfB hI_diag hx' hdiag_x'⟩⟩

end RoundTripB

/-! ## §3 Generic bounded internal injectivity (`rev_inj_internalB`, `rev_inj_internalB_lok`)

For ANY revealed singleton `R : RevEnv` (arbitrary closed index type `R.I : Sort R.uI`, family `F` at `R.f`,
constructor `mk` at `R.f + 1`, AnySort recursor `rec` at `R.f + 2`), the constant motive
`revM0 := λ (Y : R.I) (_ : F Y). R.I : Π (Y : R.I), F Y → Sort R.uI` and the identity minor
`revM0m := λ (Y : R.I). Y : Π (Y : R.I), R.I ≡ Π (Y : R.I), revM0 Y (mk Y)` extract the constructor field
`x : R.I` at level `R.uI` without using `PiRowField` or `TypedRowsWf`, and carry `LOKc σ N K` end to end. -/

section GenericInternalInj

variable {Γ : LCtx}

/-- `F a`. -/
def revFamApp (a : Expr Nat) : Expr Nat := .app (.const R.f []) a

/-- `mk a`. -/
def revMkApp (a : Expr Nat) : Expr Nat := .app (.const (R.f + 1) []) a

/-- the constant motive `λ (Y : R.I) (_ : F Y). R.I`. -/
def revM0 : Expr Nat := .lam R.I (.lam (famApp0 R.f) R.I)

/-- the identity minor `λ (Y : R.I). Y`. -/
def revM0m : Expr Nat := .lam R.I (.bvar 0)

theorem revM0_lift (c k : Nat) : lift c k R.revM0 = R.revM0 := by
  simp [revM0, lift, R.shapeE.liftI]

theorem revM0_instantiate (j : Nat) (s : Expr Nat) : instantiate j s R.revM0 = R.revM0 :=
  instantiate_of_closed _ (R.revM0_lift 0 1) j s

theorem inst_revM0_body (a : Expr Nat) :
    instantiate0 a (.lam (famApp0 R.f) R.I) = .lam (R.revFamApp a) R.I := by
  show Expr.lam (instantiate 0 a (famApp0 R.f)) (instantiate 1 (lift 0 1 a) R.I) = _
  rw [instantiate_of_closed _ (R.hclI 0)]
  rfl

theorem inst_revM0_cod (a : Expr Nat) :
    instantiate0 a (.pi (famApp0 R.f) (.sort R.uI)) = .pi (R.revFamApp a) (.sort R.uI) :=
  rfl

theorem inst_revI (s : Expr Nat) : instantiate0 s R.I = R.I :=
  instantiate_of_closed _ (R.hclI 0) 0 s

def hRevM0Body (Γ : LCtx) :
    HasTyT R.E n (.assumption R.I :: Γ) (.lam (famApp0 R.f) R.I)
      (.pi (famApp0 R.f) (.sort R.uI)) :=
  .lam _ _ .zero _ _
    (R.famTyB (.bvar _ 0 _ (by simp [lookupType, R.shapeE.liftI])))
    (R.hIEB n _)

def hRevM0 (Γ : LCtx) :
    HasTyT R.E n Γ R.revM0 (motTy R.f R.I R.uI) :=
  .lam Γ _ R.uI _ _ (R.hIEB n Γ) (R.hRevM0Body Γ)

/-- `revM0 a t ≡ R.I : Sort R.uI` by two β steps. -/
def revM0Beta {a t : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (ht : HasTyT R.E n Γ t (R.revFamApp a)) :
    ConvT R.E n Γ (.app (.app R.revM0 a) t) R.I (.sort R.uI) :=
  .trans Γ _ (.app (.lam (R.revFamApp a) R.I) t) _ _
    (.app Γ (.app R.revM0 a) (.lam (R.revFamApp a) R.I) t t
      (R.revFamApp a) (.sort R.uI)
      (castCR (R.inst_revM0_body a)
        (castT (R.inst_revM0_cod a)
          (.beta Γ R.I (.lam (famApp0 R.f) R.I) a
            (.pi (famApp0 R.f) (.sort R.uI)) R.uI (R.hIEB n Γ) (R.hRevM0Body Γ) ha)))
      (.refl Γ t _ ht))
    (castCR (R.inst_revI t)
      (ConvT.beta Γ (R.revFamApp a) R.I t (.sort R.uI) .zero
        (R.famTyB ha) (R.hIEB n _) ht))

theorem inst_minTy_revM0 :
    instantiate0 R.revM0 (minTy R.f R.I) =
      .pi R.I (.app (.app R.revM0 (.bvar 0)) (R.revMkApp (.bvar 0))) := by
  show Expr.pi (instantiate 0 R.revM0 R.I)
    (.app (.app (instantiate 1 (lift 0 1 R.revM0) (.bvar 1)) (.bvar 0))
      (.app (.const (R.f + 1) []) (.bvar 0))) = _
  rw [instantiate_of_closed _ (R.hclI 0), R.revM0_lift]
  rfl

/-- `revM0m : Π (Y : R.I), revM0 Y (mk Y)`. -/
def hRevM0m (Γ : LCtx) :
    HasTyT R.E n Γ R.revM0m
      (.pi R.I (.app (.app R.revM0 (.bvar 0)) (R.revMkApp (.bvar 0)))) :=
  let hb0 : HasTyT R.E n (.assumption R.I :: Γ) (.bvar 0) R.I :=
    .bvar _ 0 _ (by simp [lookupType, R.shapeE.liftI])
  .conv _ _ _ _ _
    (.lam Γ _ R.uI _ _ (R.hIEB n Γ) hb0)
    (.pi Γ R.I R.I R.I
      (.app (.app R.revM0 (.bvar 0)) (R.revMkApp (.bvar 0))) R.uI R.uI
      (.refl _ _ _ (R.hIEB n Γ))
      (.symm _ _ _ _ (R.revM0Beta hb0 (R.mkTyB hb0))))

/-- `revM0m a ≡ a : R.I`. -/
def revM0mAppBeta {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) :
    ConvT R.E n Γ (.app R.revM0m a) a R.I :=
  let hb0 : HasTyT R.E n (.assumption R.I :: Γ) (.bvar 0) R.I :=
    .bvar _ 0 _ (by simp [lookupType, R.shapeE.liftI])
  castT (R.inst_revI a)
    (ConvT.beta Γ R.I (.bvar 0) a R.I R.uI (R.hIEB n Γ) hb0 ha)

theorem inst_revM0mApp (a : Expr Nat) :
    instantiate0 a (.app (.app R.revM0 (.bvar 0)) (R.revMkApp (.bvar 0))) =
      .app (.app R.revM0 a) (R.revMkApp a) := by
  show Expr.app (.app (instantiate 0 a R.revM0) a) (.app (.const (R.f + 1) []) a) = _
  rw [R.revM0_instantiate]
  rfl

def hRevM0mApp {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I) :
    HasTyT R.E n Γ (.app R.revM0m a) R.I :=
  .conv _ _ _ _ _
    (castHT (R.inst_revM0mApp a) (.app _ _ _ _ _ (R.hRevM0m Γ) ha))
    (R.revM0Beta ha (R.mkTyB ha))

/-- `rec.{[R.uI]} revM0 revM0m`. -/
def revRecM0m : Expr Nat := foldApps (.const (R.f + 2) [R.uI]) [R.revM0, R.revM0m]

theorem huI_bounded : levelsBounded n [R.uI] = true := by
  simp [levelsBounded, levelBounded_mono (Nat.zero_le n) R.uI R.huI]

@[simp] theorem instI (j : Nat) (s : Expr Nat) : instantiate j s R.I = R.I :=
  instantiate_of_closed _ (R.hclI 0) j s

theorem inst_recTyG_M0m :
    instantiate0 R.revM0m (instantiate 1 (lift 0 1 R.revM0) (.pi R.I (.pi (famApp0 R.f) recB4))) =
      .pi R.I (.pi (famApp0 R.f) (.app (.app R.revM0 (.bvar 1)) (.bvar 0))) := by
  simp [instantiate0, recB4, famApp0, instantiate, lift, R.instI, R.shapeE.liftI,
    R.revM0_lift, R.revM0_instantiate]
  rfl

def hRevRecM0m (Γ : LCtx) :
    HasTyT R.E n Γ R.revRecM0m
      (.pi R.I (.pi (famApp0 R.f) (.app (.app R.revM0 (.bvar 1)) (.bvar 0)))) :=
  let hrec : HasTyT R.E n Γ (.const (R.f + 2) [R.uI]) (recTyG R.f R.I R.uI) :=
    R.recConstLB Γ R.uI R.huI_bounded
  let h1 : HasTyT R.E n Γ (.app (.const (R.f + 2) [R.uI]) R.revM0)
      (.pi (instantiate0 R.revM0 (minTy R.f R.I))
        (instantiate 1 (lift 0 1 R.revM0) (.pi R.I (.pi (famApp0 R.f) recB4)))) :=
    .app _ _ _ _ _ hrec (R.hRevM0 Γ)
  let hm0' : HasTyT R.E n Γ R.revM0m (instantiate0 R.revM0 (minTy R.f R.I)) :=
    castHT R.inst_minTy_revM0.symm (R.hRevM0m Γ)
  castHT R.inst_recTyG_M0m (.app _ _ _ _ _ h1 hm0')

theorem inst_revRecM0mY (y : Expr Nat) :
    instantiate0 y (.pi (famApp0 R.f) (.app (.app R.revM0 (.bvar 1)) (.bvar 0))) =
      .pi (R.revFamApp y) (.app (.app R.revM0 (lift 0 1 y)) (.bvar 0)) := by
  show Expr.pi (R.revFamApp y)
    (.app (.app (instantiate 1 (lift 0 1 y) R.revM0) (lift 0 1 y)) (.bvar 0)) = _
  rw [R.revM0_instantiate]

def hRevRecM0mY {y : Expr Nat} (hy : HasTyT R.E n Γ y R.I) :
    HasTyT R.E n Γ (.app R.revRecM0m y)
      (.pi (R.revFamApp y) (.app (.app R.revM0 (lift 0 1 y)) (.bvar 0))) :=
  castHT (R.inst_revRecM0mY y) (.app _ _ _ _ _ (R.hRevRecM0m Γ) hy)

theorem inst_revM0_lift (y q : Expr Nat) :
    instantiate0 q (.app (.app R.revM0 (lift 0 1 y)) (.bvar 0)) = .app (.app R.revM0 y) q := by
  show Expr.app (.app (instantiate 0 q R.revM0) (instantiate 0 q (lift 0 1 y))) q = _
  rw [R.revM0_instantiate, inst0_lift1]

def hRevRecFullB {y q : Expr Nat} (hy : HasTyT R.E n Γ y R.I)
    (hq : HasTyT R.E n Γ q (R.revFamApp y)) :
    HasTyT R.E n Γ (.app (.app R.revRecM0m y) q) R.I :=
  .conv _ _ _ _ _
    (castHT (R.inst_revM0_lift y q) (HasTyT.app _ _ _ _ _ (R.hRevRecM0mY hy) hq))
    (R.revM0Beta hy hq)

def revIotaGB {x y : Expr Nat} (hx : HasTyT R.E n Γ x R.I)
    (hy : HasTyT R.E n Γ y R.I) (hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp y)) :
    ConvT R.E n Γ (.app (.app R.revRecM0m y) (R.revMkApp x)) (.app R.revM0m x) R.I :=
  iotaOfWitness (R.revWAt R.uI [] R.revM0 R.revM0m y x)
    (R.revWAt_lhs R.uI [] R.revM0 R.revM0m y x)
    (R.revWAt_rhs R.uI [] R.revM0 R.revM0m y x)
    (R.hRevRecFullB hy hq) (R.hRevM0mApp hx)

def hRevCongB {x x' : Expr Nat} (hx' : HasTyT R.E n Γ x' R.I)
    (hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp x'))
    (hq' : HasTyT R.E n Γ (R.revMkApp x') (R.revFamApp x')) :
    ConvT R.E n Γ (.app (.app R.revRecM0m x') (R.revMkApp x))
      (.app (.app R.revRecM0m x') (R.revMkApp x')) R.I :=
  .tyConv _ _ _ _ _ R.uI
    (castT (R.inst_revM0_lift x' (R.revMkApp x))
      (ConvT.app Γ (.app R.revRecM0m x') (.app R.revRecM0m x') (R.revMkApp x) (R.revMkApp x')
        (R.revFamApp x') (.app (.app R.revM0 (lift 0 1 x')) (.bvar 0))
        (.refl _ _ _ (R.hRevRecM0mY hx'))
        (.irr _ _ _ _ (R.famTyB hx') hq hq')))
    (R.revM0Beta hx' hq)

/-- **Generic internal injectivity for ANY revealed singleton `R : RevEnv`**, in `Type` without
    tactic-block casts: given `x, x' : R.I` and `F x ≡* F x'`, produces `x ≡ x' : R.I` directly
    through `R`'s AnySort recursor at level `R.uI` (zero row premises). -/
def rev_inj_internalB {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I)
    (hx' : HasTyT R.E n Γ x' R.I) (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x')) :
    ConvT R.E n Γ x x' R.I :=
  let hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp x') := hasTyT_of_tyConv (R.mkTyB hx) hc
  let hq' : HasTyT R.E n Γ (R.revMkApp x') (R.revFamApp x') := R.mkTyB hx'
  .trans _ _ _ _ _ (.symm _ _ _ _ (R.revM0mAppBeta hx))
    (.trans _ _ _ _ _ (.symm _ _ _ _ (R.revIotaGB hx hx' hq))
      (.trans _ _ _ _ _ (R.hRevCongB hx' hq hq')
        (.trans _ _ _ _ _ (R.revIotaGB hx' hx' hq') (R.revM0mAppBeta hx'))))

end GenericInternalInj

section GenericInternalInjLok

variable {Γ : LCtx} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

theorem lok_hRevM0Body (Γ : LCtx) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKt σ N K (R.hRevM0Body (n := n) Γ) := by
  have hfam : LOKt σ N K (R.famTyB
    (HasTyT.bvar (n := n) (.assumption R.I :: Γ) 0 R.I (by simp [lookupType, R.shapeE.liftI]))) :=
    R.lok_famTyB _ trivial
  simp only [hRevM0Body, LOKt]
  exact ⟨hfam, hI _⟩

theorem lok_hRevM0 (Γ : LCtx) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKt σ N K (R.hRevM0 (n := n) Γ) := by
  simp only [hRevM0, LOKt]
  exact ⟨hI Γ, R.lok_hRevM0Body Γ hI⟩

theorem lok_revM0Beta {a t : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (ht : HasTyT R.E n Γ t (R.revFamApp a)) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K ha) (h2 : LOKt σ N K ht) :
    LOKc σ N K (R.revM0Beta ha ht) := by
  simp only [revM0Beta, LOKc, LOKc_castCR, LOKc_castT]
  exact ⟨⟨⟨hI Γ, R.lok_hRevM0Body Γ hI, h1⟩, h2⟩, R.lok_famTyB ha h1, hI _, h2⟩

theorem lok_hRevM0m (Γ : LCtx) (huIN : evalTotal σ R.uI ≤ N)
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKt σ N K (R.hRevM0m (n := n) Γ) := by
  let hb0 : HasTyT R.E n (.assumption R.I :: Γ) (.bvar 0) R.I :=
    .bvar _ 0 _ (by simp [lookupType, R.shapeE.liftI])
  have hmk : LOKt σ N K (R.mkTyB hb0) := R.lok_mkTyB hb0 trivial
  have hm : LOKc σ N K (R.revM0Beta hb0 (R.mkTyB hb0)) :=
    R.lok_revM0Beta hb0 (R.mkTyB hb0) hI trivial hmk
  change (LOKt σ N K (R.hIEB n Γ) ∧ LOKt σ N K hb0) ∧
    evalTotal σ R.uI ≤ N ∧ evalTotal σ R.uI ≤ N ∧
    LOKt σ N K (R.hIEB n Γ) ∧ LOKc σ N K (R.revM0Beta hb0 (R.mkTyB hb0))
  exact ⟨⟨hI Γ, trivial⟩, huIN, huIN, hI Γ, hm⟩

theorem lok_revM0mAppBeta {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) (h1 : LOKt σ N K ha) :
    LOKc σ N K (R.revM0mAppBeta ha) := by
  simp only [revM0mAppBeta, LOKc_castT, LOKc]
  exact ⟨hI Γ, trivial, h1⟩

theorem lok_hRevM0mApp {a : Expr Nat} (ha : HasTyT R.E n Γ a R.I)
    (huIN : evalTotal σ R.uI ≤ N) (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K ha) :
    LOKt σ N K (R.hRevM0mApp ha) := by
  change LOKt σ N K (castHT (R.inst_revM0mApp a) (.app _ _ _ _ _ (R.hRevM0m Γ) ha)) ∧
    LOKc σ N K (R.revM0Beta ha (R.mkTyB ha))
  rw [LOKt_castHT]
  exact ⟨⟨R.lok_hRevM0m Γ huIN hI, h1⟩, R.lok_revM0Beta ha (R.mkTyB ha) hI h1 (R.lok_mkTyB ha h1)⟩

theorem lok_hRevRecM0m (Γ : LCtx) (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) :
    LOKt σ N K (R.hRevRecM0m (n := n) Γ) := by
  have hKl : LevelsOK σ (K (R.f + 2)) [R.uI] := by
    intro l hl
    cases hl with
    | head => exact hK
    | tail _ h => cases h
  unfold hRevRecM0m
  rw [LOKt_castHT]
  change (LOKt σ N K (R.recConstLB Γ R.uI R.huI_bounded) ∧ LOKt σ N K (R.hRevM0 Γ)) ∧
    LOKt σ N K (castHT R.inst_minTy_revM0.symm (R.hRevM0m Γ))
  rw [LOKt_castHT]
  exact ⟨⟨R.lok_recConstLB Γ R.uI R.huI_bounded hKl, R.lok_hRevM0 Γ hI⟩, R.lok_hRevM0m Γ huIN hI⟩

theorem lok_hRevRecM0mY {y : Expr Nat} (hy : HasTyT R.E n Γ y R.I)
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ')) (h1 : LOKt σ N K hy) :
    LOKt σ N K (R.hRevRecM0mY hy) := by
  unfold hRevRecM0mY
  rw [LOKt_castHT]
  exact ⟨R.lok_hRevRecM0m Γ huIN hK hI, h1⟩

theorem lok_hRevRecFullB {y q : Expr Nat} (hy : HasTyT R.E n Γ y R.I)
    (hq : HasTyT R.E n Γ q (R.revFamApp y))
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K hy) (h2 : LOKt σ N K hq) :
    LOKt σ N K (R.hRevRecFullB hy hq) := by
  unfold hRevRecFullB
  change LOKt σ N K (castHT (R.inst_revM0_lift y q) (HasTyT.app _ _ _ _ _ (R.hRevRecM0mY hy) hq)) ∧
    LOKc σ N K (R.revM0Beta hy hq)
  rw [LOKt_castHT]
  exact ⟨⟨R.lok_hRevRecM0mY hy huIN hK hI h1, h2⟩, R.lok_revM0Beta hy hq hI h1 h2⟩

theorem lok_revIotaGB {x y : Expr Nat} (hx : HasTyT R.E n Γ x R.I)
    (hy : HasTyT R.E n Γ y R.I) (hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp y))
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hy) (h3 : LOKt σ N K hq) :
    LOKc σ N K (R.revIotaGB hx hy hq) := by
  simp only [revIotaGB, lok_iotaOfWitness]
  exact ⟨R.lok_hRevRecFullB hy hq huIN hK hI h2 h3, R.lok_hRevM0mApp hx huIN hI h1⟩

theorem lok_hRevCongB {x x' : Expr Nat} (hx' : HasTyT R.E n Γ x' R.I)
    (hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp x'))
    (hq' : HasTyT R.E n Γ (R.revMkApp x') (R.revFamApp x'))
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K hx') (h2 : LOKt σ N K hq) (h3 : LOKt σ N K hq') :
    LOKc σ N K (R.hRevCongB hx' hq hq') := by
  unfold hRevCongB
  change LOKc σ N K (castT (R.inst_revM0_lift x' (R.revMkApp x)) _) ∧
    LOKc σ N K (R.revM0Beta hx' hq)
  rw [LOKc_castT]
  exact ⟨⟨R.lok_hRevRecM0mY hx' huIN hK hI h1, R.lok_famTyB hx' h1, h2, h3⟩,
    R.lok_revM0Beta hx' hq hI h1 h2⟩

/-- **The level bound of generic internal injectivity (`rev_inj_internalB`).**
    Holds for EVERY revealed singleton `R : RevEnv` (including `riEnv` and `Foo : Nat → Prop`)
    as soon as `evalTotal σ R.uI ≤ N`, `evalTotal σ R.uI ≤ K (R.f + 2)`, and `R.hIEB` is within
    the bound. -/
theorem rev_inj_internalB_lok {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I)
    (hx' : HasTyT R.E n Γ x' R.I) (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x'))
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    LOKc σ N K (R.rev_inj_internalB hx hx' hc) := by
  let hq : HasTyT R.E n Γ (R.revMkApp x) (R.revFamApp x') := hasTyT_of_tyConv (R.mkTyB hx) hc
  let hq' : HasTyT R.E n Γ (R.revMkApp x') (R.revFamApp x') := R.mkTyB hx'
  have hq_lok : LOKt σ N K hq := LOKt_of_tyConv σ N K _ hc (R.lok_mkTyB hx h1) h3
  have hq'_lok : LOKt σ N K hq' := R.lok_mkTyB hx' h2
  change LOKc σ N K (R.revM0mAppBeta hx) ∧
    LOKc σ N K (R.revIotaGB hx hx' hq) ∧
    LOKc σ N K (R.hRevCongB hx' hq hq') ∧
    LOKc σ N K (R.revIotaGB hx' hx' hq') ∧
    LOKc σ N K (R.revM0mAppBeta hx')
  exact ⟨R.lok_revM0mAppBeta hx hI h1, R.lok_revIotaGB hx hx' hq huIN hK hI h1 h2 hq_lok,
    R.lok_hRevCongB hx' hq hq' huIN hK hI h2 hq_lok hq'_lok,
    R.lok_revIotaGB hx' hx' hq' huIN hK hI h2 h2 hq'_lok,
    R.lok_revM0mAppBeta hx' hI h2⟩

/-- Existential form for gap α on ANY revealed singleton `R : RevEnv`. -/
theorem rev_inj_internal_bounded {x x' : Expr Nat} (hx : HasTyT R.E n Γ x R.I)
    (hx' : HasTyT R.E n Γ x' R.I) (hc : TyConvT R.E n Γ (R.revFamApp x) (R.revFamApp x'))
    (huIN : evalTotal σ R.uI ≤ N) (hK : evalTotal σ R.uI ≤ K (R.f + 2))
    (hI : ∀ Γ', LOKt σ N K (R.hIEB n Γ'))
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    ∃ c : ConvT R.E n Γ x x' R.I, LOKc σ N K c :=
  ⟨R.rev_inj_internalB hx hx' hc, R.rev_inj_internalB_lok hx hx' hc huIN hK hI h1 h2 h3⟩

end GenericInternalInjLok

end RevEnv

/-! ## §4 Specialization at the class-B1 fixture `riEnv` (`riRevEnv`) -/

section FixtureLok

variable {n : Nat} {Γ : LCtx} {σ : Nat → Nat} {N : Nat} {K : Nat → Nat}

theorem riRevEnv_hIEB_eq (Γ' : LCtx) :
    riRevEnv.hIEB n Γ' = HasTyT.sort Γ' .zero :=
  RevEnv.hasTyTWeakenClosedB_sort (envClosed_of_envWfT riRevEnv.hW) .zero Γ'

theorem riRevEnv_hI_lok (hN : 2 ≤ N) (Γ' : LCtx) :
    LOKt σ N K (riRevEnv.hIEB n Γ') := by
  rw [riRevEnv_hIEB_eq]
  simp only [LOKt, evalTotal]
  omega

theorem riRevEnv_hI_diag (Γ' : LCtx) :
    DiagRecIotaTy 2 (riRevEnv.hIEB n Γ') := by
  rw [riRevEnv_hIEB_eq]
  simp only [DiagRecIotaTy]

/-- The generic internal injectivity specialized to `riEnv`, with its level bound (a second basis
    for `ri_inj_internalB_lok`). -/
theorem ri_inj_internalB_lok_generic {x x' : Expr Nat}
    (hx : HasTyT riEnv n Γ x (.sort .zero)) (hx' : HasTyT riEnv n Γ x' (.sort .zero))
    (hc : TyConvT riEnv n Γ (riApp x) (riApp x'))
    (hN : 2 ≤ N) (hK : 1 ≤ K 2)
    (h1 : LOKt σ N K hx) (h2 : LOKt σ N K hx') (h3 : LOKtc σ N K hc) :
    LOKc σ N K (riRevEnv.rev_inj_internalB hx hx' hc) :=
  riRevEnv.rev_inj_internalB_lok hx hx' hc
    (by show 0 + 1 ≤ N; omega)
    (by show 0 + 1 ≤ K 2; omega)
    (riRevEnv_hI_lok hN) h1 h2 h3

end FixtureLok

end Rcic.Syn.FamApp.Rev

#print axioms Rcic.Syn.FamApp.Rev.RevEnv.lok_bkTyB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.lok_bkConvB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.lok_bkTyConvB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.lok_trConv_selfB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.rev_inj_internalB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.rev_inj_internalB_lok
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.noRecIota_bkConvB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.diagRecIota_trConv_selfB
#print axioms Rcic.Syn.FamApp.Rev.RevEnv.twinIdxConvB_lok_and_diag
#print axioms Rcic.Syn.FamApp.Rev.ri_inj_internalB_lok_generic
