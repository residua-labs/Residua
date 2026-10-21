import rcic.RcicSynSpineComb
import rcic.RcicSynAPAlign

/-!
# Syntactic sortRow, A6 legs — constructible `buildSlotStatusAt` subdomains
(ChatGPT S10, #7352)

`research/rcic/sortrow/S10_SLOT_STATUS_BUILDERS.md`, mechanized over the landed
`DispForC`/`SpineLetPBit`/`CtxP.entrySort` machinery (`RcicSynSpineComb`), the
AP-alignment edges (`RcicSynAPAlign`), and the measures (`RcicSynPack`,
`RcicSynZetaMeasureRefute`). `closure_claim = 0`.

Two layers, kept apart exactly as the spec demands:

* `originBit σ C i` is computed **from the origin** — the sort level
  `C.entrySort i` actually recorded in the spine — never from `hA`'s bit.
* `ResolvedEntry σ C ρ i`: `resolve ρ i = .star ↔ originBit σ C i = true`.
* `AlignedEntry σ C ρ hlook hA`: `ResolvedEntry` **and**
  `originBit σ C i = levelIsZero (σ u)` — `hA` never defines the bit.

The spec's `DispEntry.zero_*`/`succ_*` walk is the landed `DispForC` spine
derivation itself (`assumption`/`letDrop`/`letInline` constructors,
discharged per-index by `resolve_eq_star_iff_of_dispForC` once the slot's
`SpineLetPBit` obligation — the real value `PBit` — is supplied). This module
adds no parallel display semantics.

`LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀` is the focus evidence S10 §4 asks the builder
to read: the real suffix `(C₀, ρ₀)`, the stored `I₀ = hA₀ : A₀ : sort u₀` and
`V₀ = hv₀ : v₀ : A₀`, the original index `i`, and the prefix path — each
`succ_*` step constrains the head clause to the shape `DispForC` itself would
record (`binderDisp` at assumptions, `.drop` with `hv.eps = .star` evidence,
`.inline (hv.eps)` otherwise).

Builders (each returns the status **and** the rank edge of every query it
issues, so a caller checks the conclusion and the descent together):

* `buildIntroducedAssumptionAtN` / `…_pi` — `Q.bitCoh PI hA` at `N = lam/pi`,
  prepaid by the landed `intro_align_pair_below` / `…_pi`; the entry is the
  `DispForC.assumption` node; `hcoh` is the strict-IH bit answer.
* `buildIntroducedLetAtN` — `N = letE`; additionally issues `PB[hv, I]`
  (`intro_let_pb_below`, the same `combMeas` drop), picks `letEntryDisp` from
  the actual `hv.eps` (`dispForC_letEntry` builds `letDrop`/`letInline`
  accordingly), then `hcoh` composes the use's prepaid gate alignment.
* `buildAmbientLetResolveAt` — `Q.pb V₀ I₀` on the ambient let's stored fields
  (`hpb : PBit σ ρ₀ hv₀ hA₀` on the focus tail, lifted into `SpineLetPBit` by
  `letSlot_spineLetPBit`); `letSlot_pb_below` is
  `combLexDM_pbit_bvar_let_zero`'s drop extended along the real focus — the
  prefix atoms join the removed block. Returns `ResolvedEntry` only; an
  arbitrary `hA` is never aligned here.
* `upgradeAlongExactOrigin` — a `ResolvedEntry` upgrades to `AlignedEntry`
  exactly when an exact-origin bit equation
  `levelIsZero (σ u₀) = levelIsZero (σ u)` is supplied (recorded forward path /
  equal recorded sorts / smaller mixed-prefix answer — all three land as the
  same `hbit`, bound to `C.entrySort i` by `hsort`).

Teeth (measurable failures, not prose):

* `pin_ambientLet_valuePBit_not_arbitrary_aligned`: the S10 control — a `.drop`
  let slot with its value `PBit` produces `ResolvedEntry`, and still refuses
  `AlignedEntry` for an `hA` whose bit differs.
* `pin_assumption_keep_resolve_not_star`: a `keep` disposition never resolves
  to `.star` — the false-bit side of the assumption entry.
* `pin_introduced_not_own_callee`: `D.wt < D.wt` refuses — an introduced
  descendant can never put `N` back as its own caller.

The full `buildSlotStatusAt` over arbitrary ambient/transported `hA` stays the
named open A6 residue; the success domain of these four functions does not
replace the original demand domain.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 the two-layer status and the origin bit -/

/-- The origin's bit: the bit of the sort level actually recorded at position
    `i` of spine `C`, under `σ` (S10 §1 — never `hA`'s bit). -/
def originBit (σ : Level → Level) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (i : Nat) : Bool :=
  match C.entrySort i with
  | some u₀ => levelIsZero (σ u₀)
  | none => false

/-- S10 §1: `ResolvedEntry` — the erased `resolve` at `i` agrees with the
    origin's own bit. -/
def ResolvedEntry (σ : Level → Level) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (ρ : List Disp) (i : Nat) : Prop :=
  resolve ρ i = .star ↔ originBit σ C i = true

/-- S10 §1: `AlignedEntry` — `ResolvedEntry` plus the gate alignment of the
    original `hA` at that same position. The bit equation is demanded, never
    folded into `originBit`. -/
def AlignedEntry (σ : Level → Level) {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    (C : CtxP E n Γ) (ρ : List Disp) {i : Nat} {A : Expr Nat} {u : Level}
    (_hlook : lookupType Γ i = some A) (_hA : TyP E n Γ A (.sort u)) : Prop :=
  ResolvedEntry σ C ρ i ∧ originBit σ C i = levelIsZero (σ u)

/-- `ResolvedEntry` discharged by the landed per-index correspondence: the
    slot's `SpineLetPBit` obligation (the value `PBit` at let slots, `True` at
    assumption slots) plus the recorded `entrySort`. -/
theorem resolvedEntry_of_dispForC {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {u₀ : Level}
    (hC : DispForC σ C ρ) (hpb : SpineLetPBit σ C ρ i)
    (hsort : C.entrySort i = some u₀) : ResolvedEntry σ C ρ i := by
  have hr := resolve_eq_star_iff_of_dispForC hC hpb hsort
  unfold ResolvedEntry originBit
  rw [hsort]
  exact hr

/-! ## §2 `LetSlot` — the real focus on an ambient let entry -/

/-- The focus: position `i` of spine `C` (display `ρ`) is a let entry with
    stored fields `hA₀`/`hv₀` over tail `(C₀, ρ₀)`. `here_*` select the slot;
    `succ_*` walk the original prefix without shortening its coordinate —
    S10 §4's "the real suffix `C₀` and `ρ₀`; the stored `I₀`/`V₀`; the original
    index and prefix path". -/
inductive LetSlot (σ : Level → Level) :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    CtxP E n Γ → List Disp → Nat →
    {Γ₀ : LCtx} → CtxP E n Γ₀ → List Disp →
    {A₀ v₀ : Expr Nat} → {u₀ : Level} →
    TyP E n Γ₀ A₀ (.sort u₀) → TyP E n Γ₀ v₀ A₀ → Prop where
  | here_drop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₀ : List Disp}
      {A₀ v₀ : Expr Nat} {u₀ : Level} {C₀ : CtxP E n Γ}
      {hA₀ : TyP E n Γ A₀ (.sort u₀)} {hv₀ : TyP E n Γ v₀ A₀}
      (hstar : hv₀.eps σ ρ₀ = .star) :
      LetSlot σ (.letBinding E n Γ A₀ u₀ v₀ C₀ hA₀ hv₀) (.drop :: ρ₀) 0
        C₀ ρ₀ hA₀ hv₀
  | here_inline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₀ : List Disp}
      {A₀ v₀ : Expr Nat} {u₀ : Level} {C₀ : CtxP E n Γ}
      {hA₀ : TyP E n Γ A₀ (.sort u₀)} {hv₀ : TyP E n Γ v₀ A₀} :
      LetSlot σ (.letBinding E n Γ A₀ u₀ v₀ C₀ hA₀ hv₀)
        (.inline (hv₀.eps σ ρ₀) :: ρ₀) 0 C₀ ρ₀ hA₀ hv₀
  | succ_assumption {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₁ : List Disp}
      {A₁ : Expr Nat} {u₁ : Level} {C₁ : CtxP E n Γ}
      {hA₁ : TyP E n Γ A₁ (.sort u₁)} {i : Nat}
      {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
      {A₀ v₀ : Expr Nat} {u₀ : Level}
      {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
      (h : LetSlot σ C₁ ρ₁ i C₀ ρ₀ hA₀ hv₀) :
      LetSlot σ (.assumption E n Γ A₁ u₁ C₁ hA₁)
        (binderDisp (levelIsZero (σ u₁)) :: ρ₁) (i + 1) C₀ ρ₀ hA₀ hv₀
  | succ_letDrop {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₁ : List Disp}
      {A₁ v₁ : Expr Nat} {u₁ : Level} {C₁ : CtxP E n Γ}
      {hA₁ : TyP E n Γ A₁ (.sort u₁)} {hv₁ : TyP E n Γ v₁ A₁} {i : Nat}
      {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
      {A₀ v₀ : Expr Nat} {u₀ : Level}
      {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
      (hstar : hv₁.eps σ ρ₁ = .star)
      (h : LetSlot σ C₁ ρ₁ i C₀ ρ₀ hA₀ hv₀) :
      LetSlot σ (.letBinding E n Γ A₁ u₁ v₁ C₁ hA₁ hv₁) (.drop :: ρ₁)
        (i + 1) C₀ ρ₀ hA₀ hv₀
  | succ_letInline {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₁ : List Disp}
      {A₁ v₁ : Expr Nat} {u₁ : Level} {C₁ : CtxP E n Γ}
      {hA₁ : TyP E n Γ A₁ (.sort u₁)} {hv₁ : TyP E n Γ v₁ A₁} {i : Nat}
      {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
      {A₀ v₀ : Expr Nat} {u₀ : Level}
      {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
      (h : LetSlot σ C₁ ρ₁ i C₀ ρ₀ hA₀ hv₀) :
      LetSlot σ (.letBinding E n Γ A₁ u₁ v₁ C₁ hA₁ hv₁)
        (.inline (hv₁.eps σ ρ₁) :: ρ₁) (i + 1) C₀ ρ₀ hA₀ hv₀

/-- The focus's recorded sort is the spine's own `entrySort`. -/
theorem letSlot_entrySort {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    (hfoc : LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀) : C.entrySort i = some u₀ := by
  induction hfoc with
  | here_drop hstar => rfl
  | here_inline => rfl
  | succ_assumption h ih => exact ih
  | succ_letDrop hstar h ih => exact ih
  | succ_letInline h ih => exact ih

/-- The `Q.pb V₀ I₀` answer at the focus tail is exactly the slot's
    `SpineLetPBit` obligation — a per-origin answer, not a whole-domain
    assumption (S10 §4). -/
theorem letSlot_spineLetPBit {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    (hfoc : LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀) :
    PBit σ ρ₀ hv₀ hA₀ → SpineLetPBit σ C ρ i := by
  induction hfoc with
  | here_drop hstar => exact fun hpb => hpb
  | here_inline => exact fun hpb => hpb
  | succ_assumption h ih => exact fun hpb => ih hpb
  | succ_letDrop hstar h ih => exact fun hpb => ih hpb
  | succ_letInline h ih => exact fun hpb => ih hpb

/-- The callee atoms `hA₀.atoms ++ hv₀.atoms ++ C₀.atoms` sit inside `C.atoms`:
    the leftover `L` is exactly the atoms of the walked prefix. -/
theorem letSlot_atoms_split (Aw : Nat → Nat) {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    (hfoc : LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀) :
    ∃ L : List Nat,
      (C.atoms Aw).Perm (L ++ (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)) := by
  induction hfoc with
  | here_drop hstar =>
      exact ⟨[], by simp only [List.nil_append]; exact List.Perm.refl _⟩
  | here_inline =>
      exact ⟨[], by simp only [List.nil_append]; exact List.Perm.refl _⟩
  | succ_assumption h ih =>
      rename_i Γ ρ₁ A₁ u₁ C₁ hA₁ i Γ₀ C₀ ρ₀ A₀ v₀ u₀ hA₀ hv₀
      obtain ⟨L, hL⟩ := ih
      refine ⟨hA₁.atoms Aw ++ L, ?_⟩
      simp only [CtxP.atoms]
      refine (List.Perm.append_left _ hL).trans ?_
      rw [List.append_assoc (hA₁.atoms Aw) L _]
  | succ_letDrop hstar h ih =>
      rename_i Γ ρ₁ A₁ v₁ u₁ C₁ hA₁ hv₁ i Γ₀ C₀ ρ₀ A₀ v₀ u₀ hA₀ hv₀
      obtain ⟨L, hL⟩ := ih
      refine ⟨(hA₁.atoms Aw ++ hv₁.atoms Aw) ++ L, ?_⟩
      simp only [CtxP.atoms]
      refine (List.Perm.append_left _ hL).trans ?_
      rw [← List.append_assoc (hA₁.atoms Aw ++ hv₁.atoms Aw) L _]
  | succ_letInline h ih =>
      rename_i Γ ρ₁ A₁ v₁ u₁ C₁ hA₁ hv₁ i Γ₀ C₀ ρ₀ A₀ v₀ u₀ hA₀ hv₀
      obtain ⟨L, hL⟩ := ih
      refine ⟨(hA₁.atoms Aw ++ hv₁.atoms Aw) ++ L, ?_⟩
      simp only [CtxP.atoms]
      refine (List.Perm.append_left _ hL).trans ?_
      rw [← List.append_assoc (hA₁.atoms Aw ++ hv₁.atoms Aw) L _]

/-- S10 §4's strict descent: `Q.pb V₀ I₀` under the let's tail spine `C₀` pays
    against any caller pair `(D, DT)` in the original context — the removed
    block is the prefix atoms plus the caller pair (nonempty via `D`), the kept
    block is exactly the let's recorded occurrences. At `i = 0` this is
    `combLexDM_pbit_bvar_let_zero`'s instance; a general index extends the same
    drop along the real focus. -/
theorem letSlot_pb_below (Aw : Nat → Nat) {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    (hfoc : LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀)
    {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) :
    DMStep (C₀.atoms Aw ++ (hv₀.atoms Aw ++ hA₀.atoms Aw))
      (C.atoms Aw ++ (D.atoms Aw ++ DT.atoms Aw)) := by
  obtain ⟨L, hL⟩ := letSlot_atoms_split Aw hfoc
  refine ⟨L ++ (D.atoms Aw ++ DT.atoms Aw), [],
    hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw, ?_, ?_, ?_, ?_⟩
  · intro hnil
    exact absurd ((List.append_eq_nil.mp
      (List.append_eq_nil.mp hnil).2).1) (TyP.atoms_ne_nil Aw D)
  · refine (hL.append_right _).trans ?_
    have e1 : (L ++ (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)) ++
        (D.atoms Aw ++ DT.atoms Aw) =
        L ++ ((hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw) ++
          (D.atoms Aw ++ DT.atoms Aw)) := List.append_assoc _ _ _
    have e2 : (L ++ (D.atoms Aw ++ DT.atoms Aw)) ++
        (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw) =
        L ++ ((D.atoms Aw ++ DT.atoms Aw) ++
          (hA₀.atoms Aw ++ hv₀.atoms Aw ++ C₀.atoms Aw)) :=
      List.append_assoc _ _ _
    rw [e1, e2]
    exact List.Perm.append_left _ List.perm_append_comm
  · show (C₀.atoms Aw ++ (hv₀.atoms Aw ++ hA₀.atoms Aw)).Perm
        ((hA₀.atoms Aw ++ hv₀.atoms Aw) ++ C₀.atoms Aw)
    exact List.perm_append_comm.trans
      (List.perm_append_comm.append_right _)
  · intro y hy
    exact absurd hy (List.not_mem_nil _)

/-! ## §3 the builders -/

theorem lookup_letBinding_zero (A₀ v : Expr Nat) (Γ : LCtx) :
    lookupType (.letBinding A₀ v :: Γ) 0 = some (lift 0 1 A₀) := by
  unfold lookupType
  rw [List.get?_cons_zero]

/-- The let entry's display is decided by the actual `hv.eps` (S10 §3):
    `letDrop` when it is `.star`, `letInline` otherwise. -/
def letEntryDisp (σ : Level → Level) (ρ₀ : List Disp)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A₀ v₀ : Expr Nat}
    (hv₀ : TyP E n Γ v₀ A₀) : Disp :=
  if hv₀.eps σ ρ₀ = .star then .drop else .inline (hv₀.eps σ ρ₀)

/-- The `DispForC` node for a let entry whose clause was decided by
    `letEntryDisp`. -/
theorem dispForC_letEntry {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level} {C₀ : CtxP E n Γ}
    {hA₀ : TyP E n Γ A₀ (.sort u₀)} {hv₀ : TyP E n Γ v₀ A₀}
    (hC₀ : DispForC σ C₀ ρ₀) :
    DispForC σ (.letBinding E n Γ A₀ u₀ v₀ C₀ hA₀ hv₀)
      (letEntryDisp σ ρ₀ hv₀ :: ρ₀) := by
  unfold letEntryDisp
  split
  · rename_i hstar
    exact .letDrop hA₀ hv₀ hC₀ hstar
  · exact .letInline hA₀ hv₀ hC₀

/-- The `PB[hv, I]` legality edge at `N = letE`: `(hv, hI)` under the ambient
    spine pays against any parent pair `(N, D₂)` — the same `combMeas` drop as
    `intro_align_pair_below_letE`, both fields strict subderivations of `N`. -/
theorem intro_let_pb_below (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ v₀ body B : Expr Nat} {u w : Level}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u)) (hv : TyP E n Γ v₀ A₀)
    (hbody : TyP E n (.letBinding A₀ v₀ :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 v₀ B) (.sort w))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂) :
    LexDM (combMeas Aw C (tyPairMeas Aw hv hI))
      (combMeas Aw C
        (tyPairMeas Aw (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT) D₂)) := by
  have hNat : (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).atoms Aw =
      [(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw] := by
    simp only [TyP.atoms]
  have hIlt : hI.wt Aw <
      (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw := by
    simp only [TyP.wt]; omega
  have hvlt : hv.wt Aw <
      (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw := by
    simp only [TyP.wt]; omega
  refine lex_of_dm ?_
  simp only [combMeas, tyPairMeas, hNat]
  refine ⟨[(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw] ++ D₂.atoms Aw,
    hv.atoms Aw ++ hI.atoms Aw, C.atoms Aw, by simp,
    List.perm_append_comm, List.perm_append_comm, ?_⟩
  intro y hy
  refine ⟨(TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw,
    List.mem_append.mpr (Or.inl (List.mem_singleton_self _)), ?_⟩
  rcases List.mem_append.mp hy with hy | hy
  · exact atoms_lt_of_wt_lt Aw hv hvlt y hy
  · exact atoms_lt_of_wt_lt Aw hI hIlt y hy

/-- S10 §2 builder (`N = lam`): the introduced assumption's slot at index 0.
    `hcoh` is the `Q.bitCoh PI hA` answer from `N`'s strict IH, its legality the
    bundled `intro_align_pair_below` edge — the two payments stay separate.
    `hC₀` is the display side's real `DispForC` for the ambient tail. -/
theorem buildIntroducedAssumptionAtN (σ : Level → Level) (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ body B : Expr Nat} {u v uA : Level} {ρ₀ : List Disp}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u))
    (hbody : TyP E n (.assumption A₀ :: Γ) body B)
    (hB : TyP E n (.assumption A₀ :: Γ) B (.sort v))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (hA : TyP E n (.assumption A₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.lam E n Γ A₀ u body B v hI hbody hB).wt Aw)
    (hC₀ : DispForC σ C ρ₀)
    (hcoh : BitCoh σ (wkAtZero (A := A₀) hI) hA) :
    AlignedEntry σ (.assumption E n Γ A₀ u C hI)
        (binderDisp (levelIsZero (σ u)) :: ρ₀) (lookup_assumption_zero A₀ Γ) hA
    ∧ LexDM (combMeas Aw (.assumption E n Γ A₀ u C hI)
              (tyPairMeas Aw (wkAtZero (A := A₀) hI) hA))
            (combMeas Aw C
              (tyPairMeas Aw (TyP.lam E n Γ A₀ u body B v hI hbody hB) D₂)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact resolvedEntry_of_dispForC (.assumption hI hC₀) True.intro rfl
  · have hb : originBit σ (.assumption E n Γ A₀ u C hI) 0 =
        levelIsZero (σ u) := rfl
    rw [hb]
    exact hcoh
  · exact intro_align_pair_below Aw C hI hbody hB D₂ hA hhA

/-- S10 §2 builder (`N = pi`): same slot, same strict-IH `hcoh`, the edge now
    `intro_align_pair_below_pi`. -/
theorem buildIntroducedAssumptionAtN_pi (σ : Level → Level) (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ B : Expr Nat} {u v uA : Level} {ρ₀ : List Disp}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u))
    (hB : TyP E n (.assumption A₀ :: Γ) B (.sort v))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (hA : TyP E n (.assumption A₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.pi E n Γ A₀ u B v hI hB).wt Aw)
    (hC₀ : DispForC σ C ρ₀)
    (hcoh : BitCoh σ (wkAtZero (A := A₀) hI) hA) :
    AlignedEntry σ (.assumption E n Γ A₀ u C hI)
        (binderDisp (levelIsZero (σ u)) :: ρ₀) (lookup_assumption_zero A₀ Γ) hA
    ∧ LexDM (combMeas Aw (.assumption E n Γ A₀ u C hI)
              (tyPairMeas Aw (wkAtZero (A := A₀) hI) hA))
            (combMeas Aw C
              (tyPairMeas Aw (TyP.pi E n Γ A₀ u B v hI hB) D₂)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact resolvedEntry_of_dispForC (.assumption hI hC₀) True.intro rfl
  · have hb : originBit σ (.assumption E n Γ A₀ u C hI) 0 =
        levelIsZero (σ u) := rfl
    rw [hb]
    exact hcoh
  · exact intro_align_pair_below_pi Aw C hI hB D₂ hA hhA

/-- S10 §3 builder (`N = letE`): the introduced let's slot at index 0, decided
    from the actual `hv.eps` via `letEntryDisp`. `hpb` is the extra
    `PB[hv, I]` request at `N` (`intro_let_pb_below`); `hcoh` is the use's
    prepaid gate alignment. Returns the `AlignedEntry` and both rank edges. -/
theorem buildIntroducedLetAtN (σ : Level → Level) (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A₀ v₀ body B : Expr Nat} {u w uA : Level} {ρ₀ : List Disp}
    (C : CtxP E n Γ)
    (hI : TyP E n Γ A₀ (.sort u)) (hv : TyP E n Γ v₀ A₀)
    (hbody : TyP E n (.letBinding A₀ v₀ :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 v₀ B) (.sort w))
    {E₂ : ResolvedEnv} {n₂ : Nat} {Γ₂ : LCtx} {e₂ T₂ : Expr Nat}
    (D₂ : TyP E₂ n₂ Γ₂ e₂ T₂)
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ) (lift 0 1 A₀) (.sort uA))
    (hhA : hA.wt Aw < (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT).wt Aw)
    (hC₀ : DispForC σ C ρ₀)
    (hpb : PBit σ ρ₀ hv hI)
    (hcoh : BitCoh σ (wkLetAtZero (A := A₀) (v := v₀) hI) hA) :
    AlignedEntry σ (.letBinding E n Γ A₀ u v₀ C hI hv)
        (letEntryDisp σ ρ₀ hv :: ρ₀) (lookup_letBinding_zero A₀ v₀ Γ) hA
    ∧ LexDM (combMeas Aw (.letBinding E n Γ A₀ u v₀ C hI hv)
              (tyPairMeas Aw (wkLetAtZero (A := A₀) (v := v₀) hI) hA))
            (combMeas Aw C
              (tyPairMeas Aw (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT)
                D₂))
    ∧ LexDM (combMeas Aw C (tyPairMeas Aw hv hI))
            (combMeas Aw C
              (tyPairMeas Aw (TyP.letE E n Γ A₀ u v₀ B body w hI hv hbody hT)
                D₂)) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact resolvedEntry_of_dispForC (dispForC_letEntry hC₀) hpb rfl
  · have hb : originBit σ (.letBinding E n Γ A₀ u v₀ C hI hv) 0 =
        levelIsZero (σ u) := rfl
    rw [hb]
    exact hcoh
  · exact intro_align_pair_below_letE Aw C hI hv hbody hT D₂ hA hhA
  · exact intro_let_pb_below Aw C hI hv hbody hT D₂

/-- S10 §4 builder: the ambient-let resolve. `hC` is the original
    `DispForC` over the real `ρ`; `hfoc` is the real prefix path to the let
    slot; `hpb` is the `Q.pb V₀ I₀` answer on the let's stored fields; the
    bundled `LexDM` is the query's strict descent. Returns `ResolvedEntry` —
    never `AlignedEntry` (S10 §4: an arbitrary `hA` still needs A6's
    mixed/prefix supply). -/
theorem buildAmbientLetResolveAt (σ : Level → Level) (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {Γ₀ : LCtx} {C₀ : CtxP E n Γ₀} {ρ₀ : List Disp}
    {A₀ v₀ : Expr Nat} {u₀ : Level}
    {hA₀ : TyP E n Γ₀ A₀ (.sort u₀)} {hv₀ : TyP E n Γ₀ v₀ A₀}
    (hC : DispForC σ C ρ)
    (hfoc : LetSlot σ C ρ i C₀ ρ₀ hA₀ hv₀)
    (hpb : PBit σ ρ₀ hv₀ hA₀)
    {e T : Expr Nat} {s : Level}
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) :
    ResolvedEntry σ C ρ i ∧
    LexDM (combMeas Aw C₀ (tyPairMeas Aw hv₀ hA₀))
          (combMeas Aw C (tyPairMeas Aw D DT)) :=
  ⟨resolvedEntry_of_dispForC hC (letSlot_spineLetPBit hfoc hpb)
      (letSlot_entrySort hfoc),
   lex_of_dm (letSlot_pb_below Aw hfoc D DT)⟩

/-- S10 §4's immediate upgrade: a `ResolvedEntry` at the exact origin becomes
    `AlignedEntry` once the origin's recorded bit is shown equal to `hA`'s —
    the recorded forward path, the equal recorded sorts, or the smaller
    mixed/prefix answer all land as the same `hbit`; `hsort` binds `u₀` to the
    actual `C.entrySort i`, so "same type" never substitutes for provenance. -/
theorem upgradeAlongExactOrigin {σ : Level → Level}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {C : CtxP E n Γ} {ρ : List Disp}
    {i : Nat} {A : Expr Nat} {u₀ u : Level}
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (hsort : C.entrySort i = some u₀) (hres : ResolvedEntry σ C ρ i)
    (hbit : levelIsZero (σ u₀) = levelIsZero (σ u)) :
    AlignedEntry σ C ρ hlook hA := by
  refine ⟨hres, ?_⟩
  unfold originBit
  rw [hsort]
  exact hbit

/-! ## §4 teeth -/

/-- CONTROL (S10 acceptance table): a `.drop` ambient let slot with only its
    value `PBit` produces `ResolvedEntry` — and still refuses `AlignedEntry`
    for an `hA` whose bit differs (`σ = id`, `u₀ = .zero` vs `uA = .succ .zero`).
    "The current erasure is star" never aligns an arbitrary `hA`. -/
theorem pin_ambientLet_valuePBit_not_arbitrary_aligned
    {E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx} {A₀ v₀ : Expr Nat}
    {C₀ : CtxP E n Γ₀} {hA₀ : TyP E n Γ₀ A₀ (.sort .zero)}
    {hv₀ : TyP E n Γ₀ v₀ A₀} {ρ₀ : List Disp}
    (hC₀ : DispForC id C₀ ρ₀)
    (hpb : PBit id ρ₀ hv₀ hA₀) (hstar : hv₀.eps id ρ₀ = .star)
    (hA : TyP E n (.letBinding A₀ v₀ :: Γ₀) (lift 0 1 A₀) (.sort (.succ .zero))) :
    ResolvedEntry id (.letBinding E n Γ₀ A₀ .zero v₀ C₀ hA₀ hv₀) (.drop :: ρ₀) 0
    ∧ ¬ AlignedEntry id (.letBinding E n Γ₀ A₀ .zero v₀ C₀ hA₀ hv₀)
        (.drop :: ρ₀) (lookup_letBinding_zero A₀ v₀ Γ₀) hA := by
  have hC : DispForC id (.letBinding E n Γ₀ A₀ .zero v₀ C₀ hA₀ hv₀)
      (.drop :: ρ₀) := .letDrop hA₀ hv₀ hC₀ hstar
  have hres := resolvedEntry_of_dispForC (i := 0) hC hpb rfl
  refine ⟨hres, ?_⟩
  intro ⟨_, hbit⟩
  have hb : originBit id (.letBinding E n Γ₀ A₀ .zero v₀ C₀ hA₀ hv₀) 0 =
      true := rfl
  have huA : levelIsZero (id (.succ .zero)) = false := rfl
  rw [hb, huA] at hbit
  exact Bool.noConfusion hbit

/-- TOOTH: the false-bit side of the assumption entry — a `keep` slot's
    `resolve` is `.bvar 0`, never `.star`. -/
theorem pin_assumption_keep_resolve_not_star {σ : Level → Level}
    {ρ₀ : List Disp} {u₀ : Level} (hz : levelIsZero (σ u₀) = false) :
    resolve (binderDisp (levelIsZero (σ u₀)) :: ρ₀) 0 ≠ .star := by
  rw [hz]
  exact ETm.noConfusion

/-- TOOTH (prepaid-position control): an introduced descendant can never put
    `N` back as its own caller — `hhA` at `hA := N` is `N.wt < N.wt`. -/
theorem pin_introduced_not_own_callee (Aw : Nat → Nat)
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E n Γ e T) : ¬ D.wt Aw < D.wt Aw :=
  Nat.lt_irrefl _

end Rcic.Syn

#print axioms Rcic.Syn.originBit
#print axioms Rcic.Syn.ResolvedEntry
#print axioms Rcic.Syn.AlignedEntry
#print axioms Rcic.Syn.resolvedEntry_of_dispForC
#print axioms Rcic.Syn.LetSlot
#print axioms Rcic.Syn.letSlot_entrySort
#print axioms Rcic.Syn.letSlot_spineLetPBit
#print axioms Rcic.Syn.letSlot_atoms_split
#print axioms Rcic.Syn.letSlot_pb_below
#print axioms Rcic.Syn.lookup_letBinding_zero
#print axioms Rcic.Syn.letEntryDisp
#print axioms Rcic.Syn.dispForC_letEntry
#print axioms Rcic.Syn.intro_let_pb_below
#print axioms Rcic.Syn.buildIntroducedAssumptionAtN
#print axioms Rcic.Syn.buildIntroducedAssumptionAtN_pi
#print axioms Rcic.Syn.buildIntroducedLetAtN
#print axioms Rcic.Syn.buildAmbientLetResolveAt
#print axioms Rcic.Syn.upgradeAlongExactOrigin
#print axioms Rcic.Syn.pin_ambientLet_valuePBit_not_arbitrary_aligned
#print axioms Rcic.Syn.pin_assumption_keep_resolve_not_star
#print axioms Rcic.Syn.pin_introduced_not_own_callee
