import rcic.RcicSynErase
import Lean

/-!
# Syntactic sortRow, S14 DISP-0 — `.drop` / `.inline .star` observational equivalence

`research/rcic/sortrow/S14_DROP_INLINE_STAR_OBS.md` §1–2 (ChatGPT, J line;
`closure_claim = 0`). Pure display algebra: no `TyP`, no context
well-formedness, no AP — additive only; `TyP.eps` and existing statements
are untouched.

`normDisp` normalizes **only the literal** `.inline .star` to `.drop`. An
`ETm` that merely *reduces* to `★` stays inlined — normalizing it would
smuggle an erased conversion into a display predicate and change the
original erasure's branch computation (§1). `DropStarEq ρ₁ ρ₂` is
observational equivalence of display lists: equal after `normDisplay`.

§2 lemmas: `DropStarEq` implies equal length, equal keep-ness at every
position, equal `countKeep` of every prefix, and equal `resolve` at every
index; `normDisplay` commutes with `removeAt` and `insertDisp`. Controls:
`.drop :: ρ` and `.inline .star :: ρ` are `DropStarEq` but never
list-equal, and the non-literal payload `.app (.lam .star) (.sort 0)` —
which `RStep`s to `★` — is not normalized.
-/

namespace Rcic.Syn

/-! ## §1 normalization — literal only -/

/-- Normalize a disposition: only a LITERAL `.inline .star` becomes `.drop`
    (S14 §1). Any other payload — including a term that reduces to `★` —
    is kept as an inline. -/
def normDisp : Disp → Disp
  | .inline .star => .drop
  | d => d

/-- Pointwise normalization of a display list. -/
def normDisplay (ρ : List Disp) : List Disp := ρ.map normDisp

/-- Observational equivalence of display lists: identical after
    literal `.inline .star ↦ .drop` normalization. -/
def DropStarEq (ρ₁ ρ₂ : List Disp) : Prop := normDisplay ρ₁ = normDisplay ρ₂

theorem DropStarEq.refl (ρ : List Disp) : DropStarEq ρ ρ := rfl

theorem DropStarEq.symm {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) :
    DropStarEq ρ₂ ρ₁ := Eq.symm h

theorem DropStarEq.trans {ρ₁ ρ₂ ρ₃ : List Disp} (h₁ : DropStarEq ρ₁ ρ₂)
    (h₂ : DropStarEq ρ₂ ρ₃) : DropStarEq ρ₁ ρ₃ := Eq.trans h₁ h₂

/-- The definition unfolded — handy for `congrArg` sites. -/
theorem DropStarEq.eq {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) :
    normDisplay ρ₁ = normDisplay ρ₂ := h

/-! ### Pointwise `normDisp` facts -/

theorem normDisp_keep : normDisp .keep = .keep := rfl

theorem normDisp_drop : normDisp .drop = .drop := rfl

theorem normDisp_inline_star : normDisp (.inline .star) = .drop := rfl

/-- A non-`.star` payload is kept — normalization is literal, never an
    erased conversion. -/
theorem normDisp_inline_ne_star {v : ETm} (h : v ≠ .star) :
    normDisp (.inline v) = .inline v := by
  cases v <;> first | exact absurd rfl h | rfl

/-- `normDisp` never creates or destroys a `.keep`. -/
theorem normDisp_eq_keep {d : Disp} : normDisp d = .keep ↔ d = .keep := by
  cases d with
  | keep => decide
  | drop => decide
  | inline v => cases v <;> first | decide | simp [normDisp]

/-- Keep-ness transfers across a single pointwise `normDisp` equation. -/
theorem keep_eq_of_normDisp_eq {d₁ d₂ : Disp} (hd : normDisp d₁ = normDisp d₂) :
    d₁ = .keep ↔ d₂ = .keep := by
  constructor
  · intro h; subst h; exact normDisp_eq_keep.mp hd.symm
  · intro h; subst h; exact normDisp_eq_keep.mp hd

/-! ## §2 pure display lemmas -/

/-- `normDisplay` reads through `getElem?` pointwise. -/
theorem getElem?_normDisplay (ρ : List Disp) (i : Nat) :
    (normDisplay ρ)[i]? = ρ[i]?.map normDisp := by
  induction ρ generalizing i with
  | nil => simp [normDisplay]
  | cons d ρ ih =>
    cases i with
    | zero => simp [normDisplay]
    | succ i => simp [normDisplay, ih]

/-- Equal lengths (S14 §2). -/
theorem DropStarEq.length_eq {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) :
    ρ₁.length = ρ₂.length := by
  simpa only [normDisplay, List.length_map] using congrArg List.length h

/-- Equal keep-ness at every position (S14 §2). -/
theorem DropStarEq.keepAt {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) (i : Nat) :
    ρ₁[i]? = some .keep ↔ ρ₂[i]? = some .keep := by
  have e : (normDisplay ρ₁)[i]? = (normDisplay ρ₂)[i]? := congrArg (·[i]?) h
  rw [getElem?_normDisplay, getElem?_normDisplay] at e
  cases h₁ : ρ₁[i]? with
  | none =>
    cases h₂ : ρ₂[i]? with
    | none => exact Iff.rfl
    | some d₂ => rw [h₁, h₂] at e; simp at e
  | some d₁ =>
    cases h₂ : ρ₂[i]? with
    | none => rw [h₁, h₂] at e; simp at e
    | some d₂ =>
      have hd : normDisp d₁ = normDisp d₂ := by
        rw [h₁, h₂] at e; simpa using e
      simp only [Option.some.injEq]
      exact keep_eq_of_normDisp_eq hd

/-- `normDisplay` preserves `countKeep` — it never touches `.keep` entries. -/
theorem countKeep_normDisplay (ρ : List Disp) :
    countKeep ρ = countKeep (normDisplay ρ) := by
  induction ρ with
  | nil => rfl
  | cons d ρ ih =>
    cases d with
    | keep => simp [countKeep, normDisplay, normDisp, ih]
    | drop => simp [countKeep, normDisplay, normDisp, ih]
    | inline v =>
      by_cases hv : v = .star
      · subst v; simp [countKeep, normDisplay, normDisp, ih]
      · simp only [normDisplay, List.map, normDisp_inline_ne_star hv, countKeep, ih]

/-- `normDisplay` commutes with `List.take`. -/
theorem normDisplay_take (ρ : List Disp) (i : Nat) :
    normDisplay (ρ.take i) = (normDisplay ρ).take i := by
  induction ρ generalizing i with
  | nil => cases i <;> rfl
  | cons d ρ ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (normDisp d :: ·) (ih i)

/-- `DropStarEq` is closed under prefixes. -/
theorem DropStarEq.take {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) (i : Nat) :
    DropStarEq (ρ₁.take i) (ρ₂.take i) := by
  show normDisplay _ = normDisplay _
  rw [normDisplay_take, normDisplay_take]
  exact congrArg (List.take i ·) h.eq

/-- Equal `countKeep` (S14 §2). -/
theorem DropStarEq.countKeep_eq {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂) :
    countKeep ρ₁ = countKeep ρ₂ := by
  rw [countKeep_normDisplay ρ₁, countKeep_normDisplay ρ₂]
  exact congrArg countKeep h.eq

/-- Equal `countKeep` of every prefix (S14 §2). -/
theorem DropStarEq.countKeep_take {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂)
    (i : Nat) : countKeep (ρ₁.take i) = countKeep (ρ₂.take i) :=
  (h.take i).countKeep_eq

/-- `resolve` never sees the difference — `.drop` and `.inline .star` resolve
    identically at every index (both `★` at `0`, both passthrough at `i+1`). -/
theorem resolve_normDisplay (ρ : List Disp) (i : Nat) :
    resolve ρ i = resolve (normDisplay ρ) i := by
  induction ρ generalizing i with
  | nil => rfl
  | cons d ρ ih =>
    cases d with
    | keep =>
      cases i with
      | zero => rfl
      | succ i => exact congrArg (·.lift 0 1) (ih i)
    | drop =>
      cases i with
      | zero => rfl
      | succ i => exact ih i
    | inline v =>
      by_cases hv : v = .star
      · subst v
        cases i with
        | zero => rfl
        | succ i => exact ih i
      · cases i with
        | zero =>
          show v = resolve (normDisp (.inline v) :: normDisplay ρ) 0
          rw [normDisp_inline_ne_star hv, resolve_inline_zero]
        | succ i =>
          show resolve ρ i = resolve (normDisp (.inline v) :: normDisplay ρ) (i + 1)
          rw [normDisp_inline_ne_star hv]
          exact ih i

/-- Equal `resolve` at every index (S14 §2). -/
theorem DropStarEq.resolve_eq {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂)
    (i : Nat) : resolve ρ₁ i = resolve ρ₂ i := by
  rw [resolve_normDisplay ρ₁ i, resolve_normDisplay ρ₂ i]
  exact congrArg (resolve · i) h.eq

/-- `normDisplay` commutes with `removeAt` (S14 §2). -/
theorem normDisplay_removeAt (ρ : List Disp) (c : Nat) :
    normDisplay (removeAt ρ c) = removeAt (normDisplay ρ) c := by
  induction ρ generalizing c with
  | nil => rfl
  | cons d ρ ih =>
    cases c with
    | zero => rfl
    | succ c => exact congrArg (normDisp d :: ·) (ih c)

/-- `normDisplay` commutes with `insertDisp` (S14 §2) — the inserted
    disposition is normalized pointwise. -/
theorem normDisplay_insertDisp (d : Disp) (j : Nat) (ρ : List Disp) :
    normDisplay (insertDisp d j ρ) = insertDisp (normDisp d) j (normDisplay ρ) := by
  induction j generalizing ρ with
  | zero => rfl
  | succ j ih =>
    cases ρ with
    | nil => rfl
    | cons d' ρ => exact congrArg (normDisp d' :: ·) (ih ρ)

/-- `DropStarEq` is preserved by `removeAt` (the wk row pays this). -/
theorem DropStarEq.removeAt {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂)
    (c : Nat) : DropStarEq (removeAt ρ₁ c) (removeAt ρ₂ c) := by
  show normDisplay _ = normDisplay _
  rw [normDisplay_removeAt, normDisplay_removeAt]
  exact congrArg (Rcic.Syn.removeAt · c) h.eq

/-- `DropStarEq` is preserved by `insertDisp` when the inserted
    dispositions are themselves observationally equal (the esub row pays
    this, with `hd := rfl` for a shared disposition). -/
theorem DropStarEq.insertDisp {ρ₁ ρ₂ : List Disp} (h : DropStarEq ρ₁ ρ₂)
    {d₁ d₂ : Disp} (hd : normDisp d₁ = normDisp d₂) (j : Nat) :
    DropStarEq (insertDisp d₁ j ρ₁) (insertDisp d₂ j ρ₂) := by
  show normDisplay _ = normDisplay _
  rw [normDisplay_insertDisp, normDisplay_insertDisp, hd]
  exact congrArg (Rcic.Syn.insertDisp (normDisp d₂) j) h.eq

/-! ## §4 controls -/

/-- Control (S14 §2): `.drop` and `.inline .star` are observationally
    equivalent but never list-equal — the equivalence is not `=`. -/
theorem dropStarEq_not_listEq :
    DropStarEq [.drop] [.inline .star] ∧ [.drop] ≠ [Disp.inline .star] :=
  ⟨rfl, by decide⟩

/-- Control (S14 §1): a payload that `RStep`s to `★` but is not literally
    `.star` is NOT normalized. `(λ★) (sort 0)` β-erases to `★`; the display
    keeps it as `.inline` — normalization is literal, never erased
    conversion. -/
theorem normDisp_nonliteral_star_payload :
    RStep [] (.app (.lam .star) (.sort .zero)) .star ∧
    normDisp (.inline (.app (.lam .star) (.sort .zero))) =
      .inline (.app (.lam .star) (.sort .zero)) :=
  ⟨RStep.beta .star (.sort .zero), rfl⟩

/-! ### Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : List Name := [
    ``Rcic.Syn.normDisp, ``Rcic.Syn.normDisplay, ``Rcic.Syn.DropStarEq,
    ``Rcic.Syn.DropStarEq.length_eq, ``Rcic.Syn.DropStarEq.keepAt,
    ``Rcic.Syn.DropStarEq.countKeep_eq, ``Rcic.Syn.DropStarEq.countKeep_take,
    ``Rcic.Syn.DropStarEq.resolve_eq,
    ``Rcic.Syn.normDisplay_removeAt, ``Rcic.Syn.normDisplay_insertDisp,
    ``Rcic.Syn.DropStarEq.removeAt, ``Rcic.Syn.DropStarEq.insertDisp,
    ``Rcic.Syn.dropStarEq_not_listEq,
    ``Rcic.Syn.normDisp_nonliteral_star_payload]
  for t in targets do
    unless env.contains t do throwError "missing declaration {t}"
    let (_, st) := ((CollectAxioms.collect t).run env).run {}
    for ax in st.axioms do
      unless [``propext, ``Quot.sound].contains ax do
        throwError "forbidden axiom {ax} in {t}"
  logInfo m!"[rcic_disp_dropstar] {targets.length} decls: axioms ⊆ [propext, Quot.sound]"

#print axioms Rcic.Syn.DropStarEq.length_eq
#print axioms Rcic.Syn.DropStarEq.keepAt
#print axioms Rcic.Syn.DropStarEq.countKeep_eq
#print axioms Rcic.Syn.DropStarEq.countKeep_take
#print axioms Rcic.Syn.DropStarEq.resolve_eq
#print axioms Rcic.Syn.normDisplay_removeAt
#print axioms Rcic.Syn.normDisplay_insertDisp
#print axioms Rcic.Syn.dropStarEq_not_listEq
#print axioms Rcic.Syn.normDisp_nonliteral_star_payload

end Rcic.Syn
