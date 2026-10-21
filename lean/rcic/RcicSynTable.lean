import rcic.RcicSynAllBelow
import rcic.RcicERScope0

/-!
# Syntactic sortRow, build step 4e — Erasure `LvlEq`-Congruence, Closedness, and `TableWF` (`deltaRule`)

`research/rcic/semantic/S3_ES_ARMS.md` §2 and §54. Discharges the Step 4 erasure-closedness,
level-congruence, and constant-rule table obligations:

1. **§1 `LvlEq`-Congruence of `TyP.eps` (`DispLvlEq`, `lvlEq_resolve`, `lvlEq_eps`,
   `lvlEq_eps_instLevel_nil`)**:
   - `DispLvlEq ρ₁ ρ₂` relates disposition lists with the same `.keep`/`.drop`/`.inline` pattern
     and `LvlEq`-related inline values.
   - `lvlEq_eps`: for **every** `D : TyP E n Γ e T` (all 15 constructors, zero extra hypotheses
     on `D`), pointwise `eqN` level maps `∀ l, eqN (σ₁ l) (σ₂ l)` and `DispLvlEq ρ₁ ρ₂` yield
     `LvlEq (D.eps σ₁ ρ₁) (D.eps σ₂ ρ₂)`.
   - `lvlEq_eps_instLevel_nil`: instantiating a closed derivation `D : TyP E a [] e T` at two
     `eqNList`-equivalent level lists `ls₁, ls₂` yields `LvlEq (D.eps (instLevel ls₁) [])
     (D.eps (instLevel ls₂) [])`, discharging `TableCongr.rhs` for `deltaRule`.

2. **§2 Closedness of `TyP.eps` (`DispClosed`, `AssumpCut`, `DispShape`, `TyP.ClosedWf`,
   `closedAt_eps`, `closedAt_eps_nil`, `eps_nil_lift_zero`, `closedWf_enrichHasTyT`)**:
   - `DispClosed ρ` asserts that each `.inline v` entry in `ρ` satisfies
     `ETm.ClosedAt (countKeep tail) v`.
   - `TyP.ClosedWf` checks only the sub-derivations evaluated by `TyP.eps`, requiring
     `AssumpCut Γ c` at `.wk` and `j = 0` at `.lsub`.
   - `closedWf_enrichHasTyT`: **every** plain typing derivation `h : HasTyT E₁ n Γ e T`
     unconditionally satisfies `(enrichHasTyT hcl hext hm hlet C h).ClosedWf` (with zero
     hypotheses on `C`, `hm`, or `hlet`).
   - `closedAt_eps`: `D.ClosedWf → DispShape Γ ρ → DispClosed ρ →
     ETm.ClosedAt (countKeep ρ) (D.eps σ ρ)`.
   - `closedAt_eps_nil` and `eps_nil_lift_zero`: every closed `D : TyP E n [] e T` with
     `D.ClosedWf` erases to a closed term `ETm.ClosedAt 0 (D.eps σ [])` fixed by `ETm.lift`
     and `ETm.inst`, discharging `TableWF.closed` and the `hlift` premise of `eps_deltaBodyInst`.

3. **§3 Constant Rules (`deltaRule`), `TableWF` Combinators, and `CvP.delta` Table Discharge**:
   - `deltaRule r D_b` packages a closed member body typing `D_b : TyP E a [] b T` as a nullary
     bare `CRule`.
   - `tableWF_singleton_deltaRule` and `tableWF_cons_deltaRule` prove `TableWF` for singleton
     and extended rule tables when `r` is fresh with respect to existing rule heads and major
     constructors.
   - `eps_deltaBodyInst_closed`, `es_of_below_delta_table_closed`, `es_of_below_delta_crule`,
     and `es_of_below_delta_crule_id` discharge `ES` for `CvP.delta` without any external `hlift`
     hypothesis.

`closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 `LvlEq`-Congruence of `TyP.eps` (`DispLvlEq`, `lvlEq_resolve`, `lvlEq_eps`) -/

/-- Pointwise `LvlEq` relation on disposition lists. -/
inductive DispLvlEq : List Disp → List Disp → Prop where
  | nil : DispLvlEq [] []
  | keep {ρ₁ ρ₂ : List Disp} :
      DispLvlEq ρ₁ ρ₂ → DispLvlEq (.keep :: ρ₁) (.keep :: ρ₂)
  | drop {ρ₁ ρ₂ : List Disp} :
      DispLvlEq ρ₁ ρ₂ → DispLvlEq (.drop :: ρ₁) (.drop :: ρ₂)
  | inline {v₁ v₂ : ETm} {ρ₁ ρ₂ : List Disp} :
      LvlEq v₁ v₂ → DispLvlEq ρ₁ ρ₂ → DispLvlEq (.inline v₁ :: ρ₁) (.inline v₂ :: ρ₂)

theorem DispLvlEq.refl : (ρ : List Disp) → DispLvlEq ρ ρ
  | [] => .nil
  | .keep :: ρ => .keep (DispLvlEq.refl ρ)
  | .drop :: ρ => .drop (DispLvlEq.refl ρ)
  | .inline v :: ρ => .inline (LvlEq.rfl' v) (DispLvlEq.refl ρ)

theorem DispLvlEq.symm {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) : DispLvlEq ρ₂ ρ₁ := by
  induction h with
  | nil => exact .nil
  | keep _ ih => exact .keep ih
  | drop _ ih => exact .drop ih
  | inline hv _ ih => exact .inline hv.symm' ih

theorem DispLvlEq.trans {ρ₁ ρ₂ ρ₃ : List Disp}
    (h₁ : DispLvlEq ρ₁ ρ₂) (h₂ : DispLvlEq ρ₂ ρ₃) : DispLvlEq ρ₁ ρ₃ := by
  induction h₁ generalizing ρ₃ with
  | nil => exact h₂
  | keep _ ih =>
      cases h₂ with
      | keep h₂' => exact .keep (ih h₂')
  | drop _ ih =>
      cases h₂ with
      | drop h₂' => exact .drop (ih h₂')
  | inline hv₁ _ ih =>
      cases h₂ with
      | inline hv₂ h₂' => exact .inline (hv₁.trans' hv₂) (ih h₂')

theorem DispLvlEq.length_eq {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    ρ₁.length = ρ₂.length := by
  induction h with
  | nil => rfl
  | keep _ ih => exact congrArg Nat.succ ih
  | drop _ ih => exact congrArg Nat.succ ih
  | inline _ _ ih => exact congrArg Nat.succ ih

theorem DispLvlEq.countKeep_eq {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    countKeep ρ₁ = countKeep ρ₂ := by
  induction h with
  | nil => rfl
  | keep _ ih => exact congrArg Nat.succ ih
  | drop _ ih => exact ih
  | inline _ _ ih => exact ih

theorem DispLvlEq.take {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    (i : Nat) → DispLvlEq (ρ₁.take i) (ρ₂.take i)
  | 0 => .nil
  | i + 1 => by
      cases h with
      | nil => exact .nil
      | keep h' => exact .keep (h'.take i)
      | drop h' => exact .drop (h'.take i)
      | inline hv h' => exact .inline hv (h'.take i)

theorem DispLvlEq.countKeep_take_eq {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) (i : Nat) :
    countKeep (ρ₁.take i) = countKeep (ρ₂.take i) :=
  (h.take i).countKeep_eq

theorem DispLvlEq.removeAt {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    (c : Nat) → DispLvlEq (removeAt ρ₁ c) (removeAt ρ₂ c)
  | 0 => by
      cases h with
      | nil => exact .nil
      | keep h' => exact h'
      | drop h' => exact h'
      | inline _ h' => exact h'
  | c + 1 => by
      cases h with
      | nil => exact .nil
      | keep h' => exact .keep (h'.removeAt c)
      | drop h' => exact .drop (h'.removeAt c)
      | inline hv h' => exact .inline hv (h'.removeAt c)

theorem DispLvlEq.insertDisp_keep {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    (j : Nat) → DispLvlEq (insertDisp .keep j ρ₁) (insertDisp .keep j ρ₂)
  | 0 => .keep h
  | j + 1 => by
      cases h with
      | nil => exact .keep .nil
      | keep h' => exact .keep (h'.insertDisp_keep j)
      | drop h' => exact .drop (h'.insertDisp_keep j)
      | inline hv h' => exact .inline hv (h'.insertDisp_keep j)

theorem DispLvlEq.insertDisp_drop {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    (j : Nat) → DispLvlEq (insertDisp .drop j ρ₁) (insertDisp .drop j ρ₂)
  | 0 => .drop h
  | j + 1 => by
      cases h with
      | nil => exact .drop .nil
      | keep h' => exact .keep (h'.insertDisp_drop j)
      | drop h' => exact .drop (h'.insertDisp_drop j)
      | inline hv h' => exact .inline hv (h'.insertDisp_drop j)

theorem DispLvlEq.insertDisp_inline {v₁ v₂ : ETm} (hv : LvlEq v₁ v₂)
    {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) :
    (j : Nat) → DispLvlEq (insertDisp (.inline v₁) j ρ₁) (insertDisp (.inline v₂) j ρ₂)
  | 0 => .inline hv h
  | j + 1 => by
      cases h with
      | nil => exact .inline hv .nil
      | keep h' => exact .keep (h'.insertDisp_inline hv j)
      | drop h' => exact .drop (h'.insertDisp_inline hv j)
      | inline hw h' => exact .inline hw (h'.insertDisp_inline hv j)

theorem DispLvlEq.getElem?_keep_cases {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) (c : Nat) :
    (ρ₁[c]? = some .keep ∧ ρ₂[c]? = some .keep) ∨
    (ρ₁[c]? ≠ some .keep ∧ ρ₂[c]? ≠ some .keep) := by
  induction h generalizing c with
  | nil =>
      simp only [List.getElem?_nil]
      exact .inr ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
  | keep _ ih =>
      cases c with
      | zero =>
          rw [List.getElem?_cons_zero, List.getElem?_cons_zero]
          exact .inl ⟨rfl, rfl⟩
      | succ c' =>
          simp only [List.getElem?_cons_succ]
          exact ih c'
  | drop _ ih =>
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero]
          exact .inr ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      | succ c' =>
          simp only [List.getElem?_cons_succ]
          exact ih c'
  | inline _ _ ih =>
      cases c with
      | zero =>
          simp only [List.getElem?_cons_zero]
          exact .inr ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
      | succ c' =>
          simp only [List.getElem?_cons_succ]
          exact ih c'

/-- `resolve` respects `DispLvlEq`. -/
theorem lvlEq_resolve {ρ₁ ρ₂ : List Disp} (h : DispLvlEq ρ₁ ρ₂) (i : Nat) :
    LvlEq (resolve ρ₁ i) (resolve ρ₂ i) := by
  induction h generalizing i with
  | nil => exact .bvar i
  | keep _ ih =>
      cases i with
      | zero => exact .bvar 0
      | succ i' => exact (ih i').lift' 0 1
  | drop _ ih =>
      cases i with
      | zero => exact .star
      | succ i' => exact ih i'
  | inline hv _ ih =>
      cases i with
      | zero => exact hv
      | succ i' => exact ih i'

theorem eqNList_map_of_pointwise {σ₁ σ₂ : Level → Level} (hσ : ∀ l, eqN (σ₁ l) (σ₂ l)) :
    (ls : List Level) → eqNList (ls.map σ₁) (ls.map σ₂)
  | [] => True.intro
  | l :: ls => ⟨hσ l, eqNList_map_of_pointwise hσ ls⟩

theorem eps_wk_not_keep_of_ne {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
    {d : LocalDecl} {c : Nat} {D : TyP E n Γ e A} {σ : Level → Level} {ρ : List Disp}
    (hk : ρ[c]? ≠ some .keep) :
    (TyP.wk E n Γ e A d c D).eps σ ρ = D.eps σ (removeAt ρ c) := by
  cases hget : ρ[c]? with
  | none => exact eps_wk_not_keep (.inl hget)
  | some disp =>
      cases disp with
      | keep => exact absurd hget hk
      | drop => exact eps_wk_not_keep (.inr (.inl hget))
      | inline v => exact eps_wk_not_keep (.inr (.inr ⟨v, hget⟩))

/-- Outer λ-erasure constructor (`★` stays `★`, any other body `eb` becomes `.lam eb`). -/
def lamOut : ETm → ETm
  | .star => .star
  | eb => .lam eb

/-- Application erasure constructor (`★` function gives `★`; `★` argument gives `ef`;
    otherwise `.app ef ea`). -/
def appOut (f a : ETm) : ETm :=
  match f with
  | .star => .star
  | ef => match a with
    | .star => ef
    | ea => .app ef ea

/-- Disposition of a let-bound value (`★` becomes `.drop`, any other `ev` becomes `.inline ev`). -/
def letDisp : ETm → Disp
  | .star => .drop
  | ev => .inline ev


theorem eps_lam_keep_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {body B : Expr Nat} {v : Level}
    (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
    (hB : TyP E n (.assumption A :: Γ) B (.sort v))
    {σ : Level → Level} (ρ : List Disp) (hu : levelIsZero (σ u) = false) :
    (TyP.lam E n Γ A u body B v hA hbody hB).eps σ ρ =
      lamOut (hbody.eps σ (.keep :: ρ)) := by
  simp only [TyP.eps, hu]
  cases hbody.eps σ (.keep :: ρ) <;> rfl

theorem eps_app_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {f a A B : Expr Nat} {w : Level}
    (hf : TyP E n Γ f (.pi A B)) (ha : TyP E n Γ a A)
    (hT : TyP E n Γ (instantiate0 a B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.app E n Γ f a A B w hf ha hT).eps σ ρ =
      appOut (hf.eps σ ρ) (ha.eps σ ρ) := rfl

theorem let_eps_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A : Expr Nat} {u : Level} {value B body : Expr Nat} {w : Level}
    (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ value A)
    (hb : TyP E n (.letBinding A value :: Γ) body B)
    (hT : TyP E n Γ (instantiate0 value B) (.sort w))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.letE E n Γ A u value B body w hA hv hb hT).eps σ ρ =
      hb.eps σ (letDisp (hv.eps σ ρ) :: ρ) := by
  simp only [TyP.eps]
  cases hv.eps σ ρ <;> rfl

theorem lsub_eps_eq {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat}
    {j : Nat} {u : Level} (D : TyP E n Γ e A) (hget : Γ[j]? = some (.letBinding t v))
    (hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u))
    (σ : Level → Level) (ρ : List Disp) :
    (TyP.lsub E n Γ e A t v j u D hget hv hvT).eps σ ρ =
      D.eps σ (insertDisp (lsubDisp (countKeep (ρ.take j)) (hv.eps σ ρ)) j ρ) := by
  simp only [TyP.eps]
  cases hv.eps σ ρ <;> rfl

theorem lvlEq_lam_match {e₁ e₂ : ETm} (h : LvlEq e₁ e₂) :
    LvlEq (lamOut e₁) (lamOut e₂) := by
  cases h with
  | star => exact .star
  | bvar i => exact .lam (.bvar i)
  | sort h => exact .lam (.sort h)
  | const r h => exact .lam (.const r h)
  | app hf ha => exact .lam (.app hf ha)
  | lam hb => exact .lam (.lam hb)
  | pi ha hb => exact .lam (.pi ha hb)

theorem lvlEq_app_match {f₁ f₂ a₁ a₂ : ETm} (hf : LvlEq f₁ f₂) (ha : LvlEq a₁ a₂) :
    LvlEq (appOut f₁ a₁) (appOut f₂ a₂) := by
  cases hf with
  | star => exact .star
  | bvar i =>
      cases ha with
      | star => exact .bvar i
      | bvar j => exact .app (.bvar i) (.bvar j)
      | sort h => exact .app (.bvar i) (.sort h)
      | const r h => exact .app (.bvar i) (.const r h)
      | app hg hx => exact .app (.bvar i) (.app hg hx)
      | lam hb => exact .app (.bvar i) (.lam hb)
      | pi ha' hb => exact .app (.bvar i) (.pi ha' hb)
  | sort h =>
      cases ha with
      | star => exact .sort h
      | bvar j => exact .app (.sort h) (.bvar j)
      | sort h' => exact .app (.sort h) (.sort h')
      | const r h' => exact .app (.sort h) (.const r h')
      | app hg hx => exact .app (.sort h) (.app hg hx)
      | lam hb => exact .app (.sort h) (.lam hb)
      | pi ha' hb => exact .app (.sort h) (.pi ha' hb)
  | const r h =>
      cases ha with
      | star => exact .const r h
      | bvar j => exact .app (.const r h) (.bvar j)
      | sort h' => exact .app (.const r h) (.sort h')
      | const r' h' => exact .app (.const r h) (.const r' h')
      | app hg hx => exact .app (.const r h) (.app hg hx)
      | lam hb => exact .app (.const r h) (.lam hb)
      | pi ha' hb => exact .app (.const r h) (.pi ha' hb)
  | app hg hx =>
      cases ha with
      | star => exact .app hg hx
      | bvar j => exact .app (.app hg hx) (.bvar j)
      | sort h => exact .app (.app hg hx) (.sort h)
      | const r h => exact .app (.app hg hx) (.const r h)
      | app hg' hx' => exact .app (.app hg hx) (.app hg' hx')
      | lam hb => exact .app (.app hg hx) (.lam hb)
      | pi ha' hb => exact .app (.app hg hx) (.pi ha' hb)
  | lam hb =>
      cases ha with
      | star => exact .lam hb
      | bvar j => exact .app (.lam hb) (.bvar j)
      | sort h => exact .app (.lam hb) (.sort h)
      | const r h => exact .app (.lam hb) (.const r h)
      | app hg hx => exact .app (.lam hb) (.app hg hx)
      | lam hb' => exact .app (.lam hb) (.lam hb')
      | pi ha' hb' => exact .app (.lam hb) (.pi ha' hb')
  | pi ha' hb =>
      cases ha with
      | star => exact .pi ha' hb
      | bvar j => exact .app (.pi ha' hb) (.bvar j)
      | sort h => exact .app (.pi ha' hb) (.sort h)
      | const r h => exact .app (.pi ha' hb) (.const r h)
      | app hg hx => exact .app (.pi ha' hb) (.app hg hx)
      | lam hb' => exact .app (.pi ha' hb) (.lam hb')
      | pi ha'' hb' => exact .app (.pi ha' hb) (.pi ha'' hb')

theorem dispLvlEq_let_match {v₁ v₂ : ETm} (hv : LvlEq v₁ v₂)
    {ρ₁ ρ₂ : List Disp} (hρ : DispLvlEq ρ₁ ρ₂) :
    DispLvlEq (letDisp v₁ :: ρ₁) (letDisp v₂ :: ρ₂) := by
  cases hv with
  | star => exact .drop hρ
  | bvar i => exact .inline (.bvar i) hρ
  | sort h => exact .inline (.sort h) hρ
  | const r h => exact .inline (.const r h) hρ
  | app hf ha => exact .inline (.app hf ha) hρ
  | lam h => exact .inline (.lam h) hρ
  | pi ha hb => exact .inline (.pi ha hb) hρ

/-- `LvlEq` transports through `localize` (each step is `inst 0 ★`, which `LvlEq.inst'`
    already covers). -/
theorem lvlEq_localize {v₁ v₂ : ETm} (h : LvlEq v₁ v₂) :
    (κ : Nat) → LvlEq (localize κ v₁) (localize κ v₂)
  | 0 => h
  | κ + 1 => lvlEq_localize (h.inst' 0 .star) κ

theorem dispLvlEq_lsub_match {v₁ v₂ : ETm} (hv : LvlEq v₁ v₂)
    {ρ₁ ρ₂ : List Disp} (hρ : DispLvlEq ρ₁ ρ₂) (j : Nat) :
    DispLvlEq (insertDisp (lsubDisp (countKeep (ρ₁.take j)) v₁) j ρ₁)
      (insertDisp (lsubDisp (countKeep (ρ₂.take j)) v₂) j ρ₂) := by
  cases hv with
  | star => exact hρ.insertDisp_drop j
  | bvar i =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.bvar i) _) j
  | sort h =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.sort h) _) j
  | const r h =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.const r h) _) j
  | app hf ha =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.app hf ha) _) j
  | lam h =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.lam h) _) j
  | pi ha hb =>
      rw [hρ.countKeep_take_eq j]
      exact hρ.insertDisp_inline (lvlEq_localize (.pi ha hb) _) j

/-- `TyP.eps` is `LvlEq`-congruent in both the level map `σ` and the disposition list `ρ`,
    for **every** `D : TyP E n Γ e T` (all 15 constructors, zero extra hypotheses). -/
theorem lvlEq_eps :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → {σ₁ σ₂ : Level → Level} →
    (∀ l, eqN (σ₁ l) (σ₂ l)) → {ρ₁ ρ₂ : List Disp} →
    DispLvlEq ρ₁ ρ₂ → LvlEq (D.eps σ₁ ρ₁) (D.eps σ₂ ρ₂)
  | _, _, _, _, _, .sort _ _ _ l _ _, _, _, hσ, _, _, _ =>
      .sort (hσ l)
  | _, _, _, _, _, .bvar _ _ _ i _ u _ _, σ₁, σ₂, hσ, _, _, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.eps, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact .star
      | false => exact lvlEq_resolve hρ i
  | _, _, _, _, _, .const _ _ _ r ls _ _ u _ _ _ _ _, σ₁, σ₂, hσ, _, _, _ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.eps, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact .star
      | false => exact .const r (eqNList_map_of_pointwise hσ ls)
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, σ₁, σ₂, hσ, _, _, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.eps, hbit]
      cases levelIsZero (σ₂ u) with
      | true =>
          exact .pi (lvlEq_eps hA hσ hρ) ((lvlEq_eps hB hσ (.drop hρ)).lift' 0 1)
      | false =>
          exact .pi (lvlEq_eps hA hσ hρ) (lvlEq_eps hB hσ (.keep hρ))
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ hA hbody hB, σ₁, σ₂, hσ, ρ₁, ρ₂, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      cases hzu : levelIsZero (σ₂ u) with
      | true =>
          rw [eps_lam_drop (hbit.trans hzu), eps_lam_drop hzu]
          exact lvlEq_eps hbody hσ (.drop hρ)
      | false =>
          rw [eps_lam_keep_eq hA hbody hB ρ₁ (hbit.trans hzu),
              eps_lam_keep_eq hA hbody hB ρ₂ hzu]
          exact lvlEq_lam_match (lvlEq_eps hbody hσ (.keep hρ))
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT, _, _, hσ, _, _, hρ => by
      rw [eps_app_eq hf ha hT, eps_app_eq hf ha hT]
      exact lvlEq_app_match (lvlEq_eps hf hσ hρ) (lvlEq_eps ha hσ hρ)
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, _, _, hσ, _, _, hρ => by
      rw [let_eps_eq hA hv hb hT, let_eps_eq hA hv hb hT]
      exact lvlEq_eps hb hσ (dispLvlEq_let_match (lvlEq_eps hv hσ hρ) hρ)
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, _, _, hσ, _, _, hρ =>
      lvlEq_eps hexp hσ hρ
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, _, _, hσ, _, _, hρ =>
      lvlEq_eps h hσ hρ
  | _, _, _, _, _, .wk _ _ _ _ _ _ c D, _, _, hσ, _, ρ₂, hρ => by
      have ih := lvlEq_eps D hσ (hρ.removeAt c)
      rcases hρ.getElem?_keep_cases c with ⟨hk₁, hk₂⟩ | ⟨hn₁, hn₂⟩
      · rw [eps_wk_keep hk₁, eps_wk_keep hk₂, hρ.countKeep_take_eq c]
        exact ih.lift' (countKeep (ρ₂.take c)) 1
      · rw [eps_wk_not_keep_of_ne hn₁, eps_wk_not_keep_of_ne hn₂]
        exact ih
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ j u D _ hv _, σ₁, σ₂, hσ, _, ρ₂, hρ => by
      have hbit : levelIsZero (σ₁ u) = levelIsZero (σ₂ u) := levelIsZero_congr (hσ u)
      simp only [TyP.eps, hbit]
      cases levelIsZero (σ₂ u) with
      | true => exact lvlEq_eps D hσ (hρ.insertDisp_drop j)
      | false =>
          rw [hρ.countKeep_take_eq j]
          exact (lvlEq_eps D hσ (hρ.insertDisp_keep j)).inst'
            (countKeep (ρ₂.take j)) (lvlEq_eps hv hσ hρ)
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D hget hv hvT, _, _, hσ, _, _, hρ => by
      rw [lsub_eps_eq D hget hv hvT, lsub_eps_eq D hget hv hvT]
      exact lvlEq_eps D hσ (dispLvlEq_lsub_match (lvlEq_eps hv hσ hρ) hρ j)
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, _, _, hσ, _, _, hρ =>
      lvlEq_eps D (fun l => hσ (instLevel ls l)) hρ
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, _, _, hσ, _, _, hρ =>
      lvlEq_eps D hσ hρ
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, _, _, hσ, _, _, hρ =>
      lvlEq_eps D hσ hρ

/-- Specialization of `lvlEq_eps` to `instLevel ls₁` and `instLevel ls₂` under `eqNList ls₁ ls₂`. -/
theorem lvlEq_eps_instLevel {E : ResolvedEnv} {a : Nat} {Γ : LCtx} {e T : Expr Nat}
    (D : TyP E a Γ e T) {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂)
    {ρ₁ ρ₂ : List Disp} (hρ : DispLvlEq ρ₁ ρ₂) :
    LvlEq (D.eps (instLevel ls₁) ρ₁) (D.eps (instLevel ls₂) ρ₂) :=
  lvlEq_eps D (instLevel_eqNList hls) hρ

/-- Specialization of `lvlEq_eps_instLevel` to `Γ = []` and `ρ₁ = ρ₂ = []`:
    instantiating any closed derivation `D : TyP E a [] e T` at two `eqNList` lists
    yields `LvlEq` erasures. -/
theorem lvlEq_eps_instLevel_nil {E : ResolvedEnv} {a : Nat} {e T : Expr Nat}
    (D : TyP E a [] e T) {ls₁ ls₂ : List Level} (hls : eqNList ls₁ ls₂) :
    LvlEq (D.eps (instLevel ls₁) []) (D.eps (instLevel ls₂) []) :=
  lvlEq_eps_instLevel D hls .nil

/-! ## §2 Closedness of `TyP.eps` (`DispClosed`, `AssumpCut`, `DispShape`, `TyP.ClosedWf`, `closedAt_eps`) -/

theorem ETm.closedAt_lift (c n : Nat) :
    {k : Nat} → {e : ETm} → ETm.ClosedAt k e → ETm.ClosedAt (k + n) (e.lift c n)
  | _, .bvar _, hc => by
      simp only [ETm.lift]
      split
      · exact Nat.add_lt_add_right hc n
      · exact Nat.lt_of_lt_of_le hc (Nat.le_add_right _ n)
  | _, .star, _ => trivial
  | _, .sort _, _ => trivial
  | _, .const _ _, _ => trivial
  | _, .app _ _, hc =>
      ⟨ETm.closedAt_lift c n hc.1, ETm.closedAt_lift c n hc.2⟩
  | k, .lam _, hc => by
      have ih := ETm.closedAt_lift (c + 1) n (k := k + 1) hc
      rwa [Nat.add_right_comm k 1 n] at ih
  | k, .pi _ _, hc => by
      have ihb := ETm.closedAt_lift (c + 1) n (k := k + 1) hc.2
      rw [Nat.add_right_comm k 1 n] at ihb
      exact ⟨ETm.closedAt_lift c n hc.1, ihb⟩

theorem ETm.closedAt_inst :
    {k j : Nat} → (hj : j ≤ k) → {r e : ETm} →
    ETm.ClosedAt k r → ETm.ClosedAt (k + 1) e → ETm.ClosedAt k (ETm.inst j r e)
  | k, _, hj, _, .bvar i, hr, he => by
      have hi : i < k + 1 := he
      simp only [ETm.inst]
      split
      · exact hr
      · split
        · rename_i hne hlt
          change i - 1 < k
          omega
        · rename_i hne hnlt
          change i < k
          omega
  | _, _, _, _, .star, _, _ => trivial
  | _, _, _, _, .sort _, _, _ => trivial
  | _, _, _, _, .const _ _, _, _ => trivial
  | _, _, hj, _, .app _ _, hr, he =>
      ⟨ETm.closedAt_inst hj hr he.1, ETm.closedAt_inst hj hr he.2⟩
  | _, _, hj, _, .lam _, hr, he =>
      ETm.closedAt_inst (Nat.succ_le_succ hj) (ETm.closedAt_lift 0 1 hr) he
  | _, _, hj, _, .pi _ _, hr, he =>
      ⟨ETm.closedAt_inst hj hr he.1,
       ETm.closedAt_inst (Nat.succ_le_succ hj) (ETm.closedAt_lift 0 1 hr) he.2⟩

/-- `inst 0 ★` drops the `ClosedAt` bound by one (the `localize` step). -/
theorem closedAt_inst0_star {n : Nat} {e : ETm} (h : ETm.ClosedAt n e) :
    ETm.ClosedAt (n - 1) (ETm.inst 0 .star e) := by
  cases n with
  | zero =>
      exact ETm.closedAt_inst (Nat.le_refl 0) trivial
        (ETm.ClosedAt.mono (Nat.zero_le 1) h)
  | succ n =>
      exact ETm.closedAt_inst (Nat.zero_le n) trivial h

/-- `localize κ` lowers the `ClosedAt` bound by `κ`: it instantiates the κ lowest
    free de-Bruijn indices with `★`. -/
theorem closedAt_localize : {n κ : Nat} → {r : ETm} →
    ETm.ClosedAt n r → ETm.ClosedAt (n - κ) (localize κ r)
  | _, 0, _, h => h
  | n, κ + 1, r, h => by
      have ih := closedAt_localize (κ := κ) (closedAt_inst0_star h)
      rwa [Nat.sub_sub n 1 κ, Nat.add_comm 1 κ] at ih

theorem lt_length_of_lookupType_some :
    {Γ : LCtx} → {i : Nat} → {A : Expr Nat} → lookupType Γ i = some A → i < Γ.length
  | [], i, _, h => by cases i <;> simp [lookupType] at h
  | _ :: Γ, 0, _, _ => Nat.zero_lt_succ Γ.length
  | _ :: _, _ + 1, _, h =>
      match lookupType_cons_succ_inv h with
      | .mk _ hlt _ => Nat.succ_lt_succ (lt_length_of_lookupType_some hlt)

/-- Each `.inline v` entry in `ρ` is `ClosedAt (countKeep tail)`. -/
inductive DispClosed : List Disp → Prop where
  | nil : DispClosed []
  | keep {ρ : List Disp} : DispClosed ρ → DispClosed (.keep :: ρ)
  | drop {ρ : List Disp} : DispClosed ρ → DispClosed (.drop :: ρ)
  | inline {v : ETm} {ρ : List Disp} :
      ETm.ClosedAt (countKeep ρ) v → DispClosed ρ → DispClosed (.inline v :: ρ)

theorem closedAt_resolve {ρ : List Disp} (h : DispClosed ρ) {i : Nat} (hi : i < ρ.length) :
    ETm.ClosedAt (countKeep ρ) (resolve ρ i) := by
  induction h generalizing i with
  | nil => nomatch hi
  | keep _ ih =>
      cases i with
      | zero => exact Nat.zero_lt_succ _
      | succ i' =>
          exact ETm.closedAt_lift 0 1 (ih (Nat.lt_of_succ_lt_succ hi))
  | drop _ ih =>
      cases i with
      | zero => exact trivial
      | succ i' => exact ih (Nat.lt_of_succ_lt_succ hi)
  | inline hv _ ih =>
      cases i with
      | zero => exact hv
      | succ i' => exact ih (Nat.lt_of_succ_lt_succ hi)

theorem countKeep_take_le : (ρ : List Disp) → (j : Nat) → countKeep (ρ.take j) ≤ countKeep ρ
  | _, 0 => Nat.zero_le _
  | [], _ + 1 => Nat.le_refl 0
  | .keep :: ρ, j + 1 => Nat.succ_le_succ (countKeep_take_le ρ j)
  | .drop :: ρ, j + 1 => countKeep_take_le ρ j
  | .inline _ :: ρ, j + 1 => countKeep_take_le ρ j

theorem countKeep_insertDisp_drop :
    (ρ : List Disp) → (j : Nat) → countKeep (insertDisp .drop j ρ) = countKeep ρ
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | .keep :: ρ, j + 1 => congrArg Nat.succ (countKeep_insertDisp_drop ρ j)
  | .drop :: ρ, j + 1 => countKeep_insertDisp_drop ρ j
  | .inline _ :: ρ, j + 1 => countKeep_insertDisp_drop ρ j

theorem countKeep_insertDisp_keep :
    (ρ : List Disp) → (j : Nat) → countKeep (insertDisp .keep j ρ) = countKeep ρ + 1
  | _, 0 => rfl
  | [], _ + 1 => rfl
  | .keep :: ρ, j + 1 => congrArg Nat.succ (countKeep_insertDisp_keep ρ j)
  | .drop :: ρ, j + 1 => countKeep_insertDisp_keep ρ j
  | .inline _ :: ρ, j + 1 => countKeep_insertDisp_keep ρ j

theorem dispClosed_insertDisp_drop {ρ : List Disp} (h : DispClosed ρ) :
    (j : Nat) → DispClosed (insertDisp .drop j ρ)
  | 0 => .drop h
  | j + 1 => by
      cases h with
      | nil => exact .drop .nil
      | keep h' => exact .keep (dispClosed_insertDisp_drop h' j)
      | drop h' => exact .drop (dispClosed_insertDisp_drop h' j)
      | inline hv h' =>
          refine .inline ?_ (dispClosed_insertDisp_drop h' j)
          rw [countKeep_insertDisp_drop]
          exact hv

theorem dispClosed_insertDisp_keep {ρ : List Disp} (h : DispClosed ρ) :
    (j : Nat) → DispClosed (insertDisp .keep j ρ)
  | 0 => .keep h
  | j + 1 => by
      cases h with
      | nil => exact .keep .nil
      | keep h' => exact .keep (dispClosed_insertDisp_keep h' j)
      | drop h' => exact .drop (dispClosed_insertDisp_keep h' j)
      | inline hv h' =>
          refine .inline ?_ (dispClosed_insertDisp_keep h' j)
          rw [countKeep_insertDisp_keep]
          exact ETm.ClosedAt.mono (Nat.le_succ _) hv

/-- The first `c` entries of `Γ` exist and are `.assumption` declarations
    (combines `c ≤ Γ.length` and `AssumptionPrefix Γ c`). -/
inductive AssumpCut : LCtx → Nat → Prop where
  | zero (Γ : LCtx) : AssumpCut Γ 0
  | succ (A : Expr Nat) {Γ : LCtx} {c : Nat} :
      AssumpCut Γ c → AssumpCut (.assumption A :: Γ) (c + 1)

theorem AssumpCut.le_length {Γ : LCtx} {c : Nat} (h : AssumpCut Γ c) : c ≤ Γ.length := by
  induction h with
  | zero _ => exact Nat.zero_le _
  | succ _ _ ih => exact Nat.succ_le_succ ih

theorem AssumpCut.assumptionPrefix {Γ : LCtx} {c : Nat} (h : AssumpCut Γ c) :
    AssumptionPrefix Γ c := by
  induction h with
  | zero Γ => exact assumptionPrefix_zero Γ
  | succ A _ ih => exact assumptionPrefix_succ_assumption A _ _ ih

/-- Structural alignment between a local context `Γ` and a disposition list `ρ`. -/
inductive DispShape : LCtx → List Disp → Prop where
  | nil : DispShape [] []
  | assumptionKeep {A : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DispShape Γ ρ → DispShape (.assumption A :: Γ) (.keep :: ρ)
  | assumptionDrop {A : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DispShape Γ ρ → DispShape (.assumption A :: Γ) (.drop :: ρ)
  | letDrop {A v : Expr Nat} {Γ : LCtx} {ρ : List Disp} :
      DispShape Γ ρ → DispShape (.letBinding A v :: Γ) (.drop :: ρ)
  | letInline {A v : Expr Nat} {w : ETm} {Γ : LCtx} {ρ : List Disp} :
      DispShape Γ ρ → DispShape (.letBinding A v :: Γ) (.inline w :: ρ)

theorem DispShape.length_eq {Γ : LCtx} {ρ : List Disp} (h : DispShape Γ ρ) :
    ρ.length = Γ.length := by
  induction h with
  | nil => rfl
  | assumptionKeep _ ih => exact congrArg Nat.succ ih
  | assumptionDrop _ ih => exact congrArg Nat.succ ih
  | letDrop _ ih => exact congrArg Nat.succ ih
  | letInline _ ih => exact congrArg Nat.succ ih

theorem dispShape_binderDisp {A : Expr Nat} {Γ : LCtx} {ρ : List Disp}
    (b : Bool) (h : DispShape Γ ρ) :
    DispShape (.assumption A :: Γ) (binderDisp b :: ρ) := by
  cases b with
  | true => exact .assumptionDrop h
  | false => exact .assumptionKeep h

theorem dispShape_of_dispFor {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : DispFor σ E n Γ ρ) : DispShape Γ ρ := by
  induction h with
  | nil _ => exact .nil
  | assumption _ _ ih => exact dispShape_binderDisp _ ih
  | letDrop _ _ _ _ ih => exact .letDrop ih
  | letInline _ _ _ ih => exact .letInline ih

theorem dispShape_of_ctxP (σ : Level → Level) {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → DispShape Γ (C.disp σ)
  | _, .nil _ _ => .nil
  | _, .assumption _ _ _ _ u hC _ => by
      simp only [CtxP.disp]
      cases levelIsZero (σ u) with
      | true => exact .assumptionDrop (dispShape_of_ctxP σ hC)
      | false => exact .assumptionKeep (dispShape_of_ctxP σ hC)
  | _, .letBinding _ _ _ _ _ _ hC _ _ =>
      .letInline (dispShape_of_ctxP σ hC)

theorem dispShape_cctx {A A' : Expr Nat} {Γ : LCtx} {ρ : List Disp}
    (h : DispShape (.assumption A' :: Γ) ρ) : DispShape (.assumption A :: Γ) ρ := by
  cases h with
  | assumptionKeep h₀ => exact .assumptionKeep h₀
  | assumptionDrop h₀ => exact .assumptionDrop h₀

theorem dispShape_of_instLvlsCtx (ls : List Level) :
    {Γ : LCtx} → {ρ : List Disp} → DispShape (instLvlsCtx ls Γ) ρ → DispShape Γ ρ
  | [], _, h => by
      cases h
      exact .nil
  | .assumption _ :: _, _, h => by
      cases h with
      | assumptionKeep h₀ => exact .assumptionKeep (dispShape_of_instLvlsCtx ls h₀)
      | assumptionDrop h₀ => exact .assumptionDrop (dispShape_of_instLvlsCtx ls h₀)
  | .letBinding _ _ :: _, _, h => by
      cases h with
      | letDrop h₀ => exact .letDrop (dispShape_of_instLvlsCtx ls h₀)
      | letInline h₀ => exact .letInline (dispShape_of_instLvlsCtx ls h₀)

theorem dispShape_insertDisp_drop (v : Expr Nat) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} → Γ[j]? = some (.assumption t) →
    {ρ : List Disp} → DispShape (substRemove v j Γ) ρ → DispShape Γ (insertDisp .drop j ρ)
  | [], j, _, hget, _, _ => by cases j <;> cases hget
  | d :: _, 0, _, hget, _, hs => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact .assumptionDrop hs
  | .assumption _ :: _, j + 1, _, hget, _, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | assumptionKeep hs₀ => exact .assumptionKeep (dispShape_insertDisp_drop v (j := j) hget hs₀)
      | assumptionDrop hs₀ => exact .assumptionDrop (dispShape_insertDisp_drop v (j := j) hget hs₀)
  | .letBinding _ _ :: _, j + 1, _, hget, _, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | letDrop hs₀ => exact .letDrop (dispShape_insertDisp_drop v (j := j) hget hs₀)
      | letInline hs₀ => exact .letInline (dispShape_insertDisp_drop v (j := j) hget hs₀)

theorem dispShape_insertDisp_keep (v : Expr Nat) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} → Γ[j]? = some (.assumption t) →
    {ρ : List Disp} → DispShape (substRemove v j Γ) ρ → DispShape Γ (insertDisp .keep j ρ)
  | [], j, _, hget, _, _ => by cases j <;> cases hget
  | d :: _, 0, _, hget, _, hs => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact .assumptionKeep hs
  | .assumption _ :: _, j + 1, _, hget, _, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | assumptionKeep hs₀ => exact .assumptionKeep (dispShape_insertDisp_keep v (j := j) hget hs₀)
      | assumptionDrop hs₀ => exact .assumptionDrop (dispShape_insertDisp_keep v (j := j) hget hs₀)
  | .letBinding _ _ :: _, j + 1, _, hget, _, hs => by
      simp only [List.getElem?_cons_succ] at hget
      cases hs with
      | letDrop hs₀ => exact .letDrop (dispShape_insertDisp_keep v (j := j) hget hs₀)
      | letInline hs₀ => exact .letInline (dispShape_insertDisp_keep v (j := j) hget hs₀)

theorem dispShape_let_clause {A v : Expr Nat} {Γ : LCtx} {ρ : List Disp}
    (hs : DispShape Γ ρ) (ev : ETm) :
    DispShape (.letBinding A v :: Γ) (letDisp ev :: ρ) := by
  cases ev with
  | star => exact .letDrop hs
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ => exact .letInline hs

theorem dispClosed_let_clause {ρ : List Disp} (hc : DispClosed ρ)
    {ev : ETm} (hev : ETm.ClosedAt (countKeep ρ) ev) :
    DispClosed (letDisp ev :: ρ) := by
  cases ev with
  | star => exact .drop hc
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ => exact .inline hev hc

theorem countKeep_let_clause (ρ : List Disp) (ev : ETm) :
    countKeep (letDisp ev :: ρ) = countKeep ρ := by
  cases ev <;> rfl

theorem dispShape_insertDisp_let (v : Expr Nat) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} →
    j = 0 → Γ[j]? = some (.letBinding t v) →
    {ρ : List Disp} → DispShape (substRemove v j Γ) ρ → (ev : ETm) →
    DispShape Γ (insertDisp (letDisp ev) j ρ)
  | [], 0, _, _, hget, _, _, _ => by cases hget
  | d :: _, 0, _, _, hget, _, hs, ev => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact dispShape_let_clause hs ev

theorem dispClosed_insertDisp_let {j : Nat} (hj : j = 0) {ρ : List Disp} (hc : DispClosed ρ)
    {ev : ETm} (hev : ETm.ClosedAt (countKeep ρ) ev) :
    DispClosed (insertDisp (letDisp ev) j ρ) := by
  subst hj
  exact dispClosed_let_clause hc hev

theorem countKeep_insertDisp_let {j : Nat} (hj : j = 0) (ρ : List Disp) (ev : ETm) :
    countKeep (insertDisp (letDisp ev) j ρ) = countKeep ρ := by
  subst hj
  exact countKeep_let_clause ρ ev

theorem dispShape_lsub_clause {A v : Expr Nat} {Γ : LCtx} {ρ : List Disp}
    (hs : DispShape Γ ρ) (κ : Nat) (ev : ETm) :
    DispShape (.letBinding A v :: Γ) (lsubDisp κ ev :: ρ) := by
  cases ev with
  | star => exact .letDrop hs
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ => exact .letInline hs

theorem dispClosed_lsub_clause {ρ : List Disp} (hc : DispClosed ρ) (κ : Nat)
    {ev : ETm} (hev : ETm.ClosedAt (countKeep ρ) ev) :
    DispClosed (lsubDisp κ ev :: ρ) := by
  cases ev with
  | star => exact .drop hc
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ =>
      exact .inline (ETm.ClosedAt.mono (Nat.sub_le _ _) (closedAt_localize hev)) hc

theorem countKeep_lsub_clause (ρ : List Disp) (κ : Nat) (ev : ETm) :
    countKeep (lsubDisp κ ev :: ρ) = countKeep ρ := by
  cases ev <;> rfl

theorem dispShape_insertDisp_lsub (v : Expr Nat) :
    {Γ : LCtx} → {j : Nat} → {t : Expr Nat} →
    (hj : j = 0) → Γ[j]? = some (.letBinding t v) →
    {ρ : List Disp} → DispShape (substRemove v j Γ) ρ → (κ : Nat) → (ev : ETm) →
    DispShape Γ (insertDisp (lsubDisp κ ev) j ρ)
  | [], 0, _, _, hget, _, _, _, _ => by cases hget
  | _ :: _, 0, _, _, hget, _, hs, κ, ev => by
      simp only [List.getElem?_cons_zero] at hget
      cases Option.some.inj hget
      exact dispShape_lsub_clause hs κ ev

theorem dispClosed_insertDisp_lsub {j : Nat} (hj : j = 0) {ρ : List Disp} (hc : DispClosed ρ)
    (κ : Nat) {ev : ETm} (hev : ETm.ClosedAt (countKeep ρ) ev) :
    DispClosed (insertDisp (lsubDisp κ ev) j ρ) := by
  subst hj
  exact dispClosed_lsub_clause hc κ hev

theorem countKeep_insertDisp_lsub {j : Nat} (hj : j = 0) (ρ : List Disp) (κ : Nat) (ev : ETm) :
    countKeep (insertDisp (lsubDisp κ ev) j ρ) = countKeep ρ := by
  subst hj
  exact countKeep_lsub_clause ρ κ ev

/-- Step lemma for `TyP.wk` under `AssumpCut Γ c`: `removeAt ρ c` preserves both
    `DispShape` and `DispClosed` and tracks `countKeep` according to `ρ[c]?`. -/
theorem wk_closed_step (d : LocalDecl) {Γ : LCtx} {c : Nat} (ha : AssumpCut Γ c)
    {ρ : List Disp} (hs : DispShape (insertAt d c Γ) ρ) (hc : DispClosed ρ) :
    DispShape Γ (removeAt ρ c) ∧ DispClosed (removeAt ρ c) ∧
    ((ρ[c]? = some .keep ∧ countKeep ρ = countKeep (removeAt ρ c) + 1) ∨
     (ρ[c]? ≠ some .keep ∧ countKeep (removeAt ρ c) = countKeep ρ)) := by
  induction ha generalizing ρ with
  | zero Γ₀ =>
      cases hs with
      | assumptionKeep hs₀ =>
          cases hc with
          | keep hc₀ =>
              rw [List.getElem?_cons_zero]
              exact ⟨hs₀, hc₀, .inl ⟨rfl, rfl⟩⟩
      | assumptionDrop hs₀ =>
          cases hc with
          | drop hc₀ =>
              simp only [List.getElem?_cons_zero]
              exact ⟨hs₀, hc₀, .inr ⟨(fun h => nomatch h), rfl⟩⟩
      | letDrop hs₀ =>
          cases hc with
          | drop hc₀ =>
              simp only [List.getElem?_cons_zero]
              exact ⟨hs₀, hc₀, .inr ⟨(fun h => nomatch h), rfl⟩⟩
      | letInline hs₀ =>
          cases hc with
          | inline _ hc₀ =>
              simp only [List.getElem?_cons_zero]
              exact ⟨hs₀, hc₀, .inr ⟨(fun h => nomatch h), rfl⟩⟩
  | succ A _ ih =>
      cases hs with
      | assumptionKeep hs₀ =>
          cases hc with
          | keep hc₀ =>
              obtain ⟨hs', hc', hck⟩ := ih hs₀ hc₀
              refine ⟨.assumptionKeep hs', .keep hc', ?_⟩
              simp only [List.getElem?_cons_succ]
              rcases hck with ⟨hk, hcnt⟩ | ⟨hnk, hcnt⟩
              · exact .inl ⟨hk, by simp only [countKeep, removeAt, hcnt]⟩
              · exact .inr ⟨hnk, by simp only [countKeep, removeAt, hcnt]⟩
      | assumptionDrop hs₀ =>
          cases hc with
          | drop hc₀ =>
              obtain ⟨hs', hc', hck⟩ := ih hs₀ hc₀
              refine ⟨.assumptionDrop hs', .drop hc', ?_⟩
              simp only [List.getElem?_cons_succ]
              rcases hck with ⟨hk, hcnt⟩ | ⟨hnk, hcnt⟩
              · exact .inl ⟨hk, by simp only [countKeep, removeAt, hcnt]⟩
              · exact .inr ⟨hnk, by simp only [countKeep, removeAt, hcnt]⟩

/-- Erasure-spine well-formedness for closedness: checks only the sub-derivations
    actually evaluated by `TyP.eps`, requiring `AssumpCut Γ c` at `.wk` and `j = 0` at `.lsub`. -/
def TyP.ClosedWf : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyP E n Γ e T → Prop
  | _, _, _, _, _, .sort .. => True
  | _, _, _, _, _, .bvar .. => True
  | _, _, _, _, _, .const .. => True
  | _, _, _, _, _, .pi _ _ _ _ _ _ _ hA hB => hA.ClosedWf ∧ hB.ClosedWf
  | _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ hbody _ => hbody.ClosedWf
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha _ => hf.ClosedWf ∧ ha.ClosedWf
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ hv hb _ => hv.ClosedWf ∧ hb.ClosedWf
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.ClosedWf
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _ => h.ClosedWf
  | _, _, _, _, _, .wk _ _ Γ _ _ _ c D => AssumpCut Γ c ∧ D.ClosedWf
  | _, _, _, _, _, .esub _ _ _ _ _ _ _ _ _ D _ hv _ => D.ClosedWf ∧ hv.ClosedWf
  | _, _, _, _, _, .lsub _ _ _ _ _ _ _ j _ D _ hv _ => j = 0 ∧ D.ClosedWf ∧ hv.ClosedWf
  | _, _, _, _, _, .linst _ _ _ _ _ _ _ _ _ D => D.ClosedWf
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D => D.ClosedWf
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _ => D.ClosedWf

/-- Context-level `ClosedWf`: every let-value in `C` satisfies `TyP.ClosedWf`. -/
def CtxP.ClosedWf {E : ResolvedEnv} {n : Nat} : {Γ : LCtx} → CtxP E n Γ → Prop
  | _, .nil _ _ => True
  | _, .assumption _ _ _ _ _ hC _ => hC.ClosedWf
  | _, .letBinding _ _ _ _ _ _ hC _ hv => hC.ClosedWf ∧ hv.ClosedWf

theorem closedWf_tyCast {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e e' T T' : Expr Nat}
    (he : e = e') (hT : T = T') {D : TyP E n Γ e T} (hD : D.ClosedWf) :
    (tyCast he hT D).ClosedWf := by
  subst he; subst hT; exact hD

theorem closedWf_tyCastCtx {E : ResolvedEnv} {n : Nat} {Γ Γ' : LCtx} {e T : Expr Nat}
    (hΓ : Γ = Γ') {D : TyP E n Γ e T} (hD : D.ClosedWf) :
    (tyCastCtx hΓ D).ClosedWf := by
  subst hΓ; exact hD

theorem closedWf_castLift0 {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {v t : Expr Nat} {D : TyP E n Γ v t} (hD : D.ClosedWf) :
    (castLift0 D).ClosedWf :=
  closedWf_tyCast _ _ hD

theorem closedWf_wkAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A : Expr Nat}
    {D : TyP E n Γ e T} (hD : D.ClosedWf) :
    (wkAtZero (A := A) D).ClosedWf :=
  closedWf_tyCastCtx _ ⟨.zero Γ, hD⟩

theorem closedWf_wkLetAtZero {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T A v : Expr Nat}
    {D : TyP E n Γ e T} (hD : D.ClosedWf) :
    (wkLetAtZero (A := A) (v := v) D).ClosedWf :=
  closedWf_tyCastCtx _ ⟨.zero Γ, hD⟩

theorem closedWf_wkClosed {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    (hcle : lift 0 1 e = e) (hclT : lift 0 1 T = T) :
    (Γ : LCtx) → {D : TyP E n [] e T} → D.ClosedWf →
      (wkClosed hcle hclT Γ D).ClosedWf
  | [], _, hD => hD
  | _ :: Γ, _, hD =>
      closedWf_tyCast _ _ (closedWf_tyCastCtx _ ⟨.zero Γ, closedWf_wkClosed hcle hclT Γ hD⟩)

theorem closedWf_deltaBodyInst {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) {D_b : TyP E m.arity [] b m.mtype} (hD : D_b.ClosedWf) :
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b).ClosedWf :=
  closedWf_wkClosed _ _ Γ hD

theorem closedWf_instEnd {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A body B arg : Expr Nat} {u : Level}
    {hb : TyP E n (.assumption A :: Γ) body B}
    {ha : TyP E n Γ arg A} {hA : TyP E n Γ A (.sort u)}
    (hbW : hb.ClosedWf) (haW : ha.ClosedWf) :
    (instEnd hb ha hA).ClosedWf := by
  unfold instEnd
  refine closedWf_tyCast _ _ ?_
  exact ⟨hbW, closedWf_castLift0 haW⟩

theorem closedWf_letSub {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    {hv : TyP E n Γ value A} {hA : TyP E n Γ A (.sort u)}
    (hbW : hb.ClosedWf) (hvW : hv.ClosedWf) :
    (letSub hb hv hA).ClosedWf := by
  unfold letSub
  refine closedWf_tyCast _ _ ?_
  exact ⟨rfl, hbW, closedWf_castLift0 hvW⟩

theorem closedWf_trLetNorm {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hvW : hv.ClosedWf) (hbW : hb.ClosedWf) :
    (trLetNorm hA hv hb).ClosedWf :=
  closedWf_letSub hbW hvW

theorem closedWf_trLetE {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {A value body B : Expr Nat} {u : Level}
    (hA : TyP E n Γ A (.sort u)) {hv : TyP E n Γ value A}
    {hb : TyP E n (.letBinding A value :: Γ) body B}
    (hvW : hv.ClosedWf) (hbW : hb.ClosedWf) :
    (trLetE hA hv hb).ClosedWf :=
  ⟨hvW, hbW⟩

/-- Every plain typing derivation `h : HasTyT E₁ n Γ e T` unconditionally satisfies
    `(enrichHasTyT hcl hext hm hlet C h).ClosedWf`, with zero hypotheses on `C`, `hm`, or `hlet`. -/
theorem closedWf_enrichHasTyT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → (C : CtxP E n Γ) → {e T : Expr Nat} → (h : HasTyT E₁ n Γ e T) →
      (enrichHasTyT hcl hext hm hlet C h).ClosedWf
  | _, _, _, _, .sort _ _ => trivial
  | _, _, _, _, .bvar _ _ _ _ => trivial
  | _, _, _, _, .const _ _ _ _ _ _ _ => trivial
  | _, C, _, _, .pi _ _ _ _ _ hA hB =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hA,
       closedWf_enrichHasTyT hcl hext hm hlet _ hB⟩
  | _, _, _, _, .lam _ _ _ _ _ _ hbody =>
      closedWf_enrichHasTyT hcl hext hm hlet _ hbody
  | _, C, _, _, .app _ _ _ _ _ hf ha =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hf,
       closedWf_enrichHasTyT hcl hext hm hlet C ha⟩
  | _, C, _, _, .letE _ _ _ _ _ _ _ hv hb =>
      ⟨closedWf_enrichHasTyT hcl hext hm hlet C hv,
       closedWf_enrichHasTyT hcl hext hm hlet _ hb⟩
  | _, C, _, _, .lit _ _ _ hexp =>
      closedWf_enrichHasTyT hcl hext hm hlet C hexp
  | _, C, _, _, .conv _ _ _ _ _ h _ =>
      closedWf_enrichHasTyT hcl hext hm hlet C h

/-- Every plain well-formed context `hΓ : CtxWfT E₁ n Γ` unconditionally satisfies
    `(enrichCtxWfT hcl hext hm hlet hΓ).ClosedWf`. -/
theorem closedWf_enrichCtxWfT {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n) :
    {Γ : LCtx} → (hΓ : CtxWfT E₁ n Γ) → (enrichCtxWfT hcl hext hm hlet hΓ).ClosedWf
  | _, .nil => trivial
  | _, .assumption _ _ _ hΓ₀ _ =>
      closedWf_enrichCtxWfT hcl hext hm hlet hΓ₀
  | _, .letBinding _ _ _ _ hΓ₀ _ hv =>
      ⟨closedWf_enrichCtxWfT hcl hext hm hlet hΓ₀,
       closedWf_enrichHasTyT hcl hext hm hlet _ hv⟩

theorem closedAt_lam_match {k : Nat} {e : ETm} (h : ETm.ClosedAt (k + 1) e) :
    ETm.ClosedAt k (lamOut e) := by
  cases e with
  | star => exact trivial
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ => exact h

theorem closedAt_app_match {k : Nat} {f a : ETm}
    (hf : ETm.ClosedAt k f) (ha : ETm.ClosedAt k a) :
    ETm.ClosedAt k (appOut f a) := by
  cases f with
  | star => exact trivial
  | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ =>
      cases a with
      | star => exact hf
      | bvar _ | sort _ | const _ _ | app _ _ | lam _ | pi _ _ => exact ⟨hf, ha⟩

/-- Main closedness theorem for `TyP.eps`: under `D.ClosedWf`, `DispShape Γ ρ`, and
    `DispClosed ρ`, `D.eps σ ρ` has all free de Bruijn indices strictly below `countKeep ρ`. -/
theorem closedAt_eps :
    {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    (D : TyP E n Γ e T) → D.ClosedWf → (σ : Level → Level) →
    {ρ : List Disp} → DispShape Γ ρ → DispClosed ρ →
    ETm.ClosedAt (countKeep ρ) (D.eps σ ρ)
  | _, _, _, _, _, .sort .., _, _, _, _, _ => trivial
  | _, _, _, _, _, .bvar _ _ _ i _ u hlook _, _, σ, ρ, hs, hc => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) with
      | true => exact trivial
      | false =>
          have hi : i < ρ.length := hs.length_eq.symm ▸ lt_length_of_lookupType_some hlook
          exact closedAt_resolve hc hi
  | _, _, _, _, _, .const .., _, σ, _, _, _ => by
      simp only [TyP.eps]
      cases levelIsZero (σ _) <;> exact trivial
  | _, _, _, _, _, .pi _ _ _ _ u _ _ hA hB, hW, σ, _, hs, hc => by
      simp only [TyP.eps]
      have ihA := closedAt_eps hA hW.1 σ hs hc
      cases levelIsZero (σ u) with
      | true =>
          have ihB := closedAt_eps hB hW.2 σ (.assumptionDrop hs) (.drop hc)
          exact ⟨ihA, ETm.closedAt_lift 0 1 ihB⟩
      | false =>
          have ihB := closedAt_eps hB hW.2 σ (.assumptionKeep hs) (.keep hc)
          exact ⟨ihA, ihB⟩
  | _, _, _, _, _, .lam _ _ _ _ u _ _ _ hA hbody hB, hbW, σ, ρ, hs, hc => by
      cases hzu : levelIsZero (σ u) with
      | true =>
          rw [eps_lam_drop hzu]
          exact closedAt_eps hbody hbW σ (.assumptionDrop hs) (.drop hc)
      | false =>
          rw [eps_lam_keep_eq hA hbody hB ρ hzu]
          exact closedAt_lam_match (closedAt_eps hbody hbW σ (.assumptionKeep hs) (.keep hc))
  | _, _, _, _, _, .app _ _ _ _ _ _ _ _ hf ha hT, hW, σ, ρ, hs, hc => by
      rw [eps_app_eq hf ha hT]
      exact closedAt_app_match (closedAt_eps hf hW.1 σ hs hc) (closedAt_eps ha hW.2 σ hs hc)
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ hA hv hb hT, hW, σ, ρ, hs, hc => by
      rw [let_eps_eq hA hv hb hT]
      have ihv := closedAt_eps hv hW.1 σ hs hc
      have ihb := closedAt_eps hb hW.2 σ
        (dispShape_let_clause hs (hv.eps σ ρ))
        (dispClosed_let_clause hc ihv)
      rwa [countKeep_let_clause] at ihb
  | _, _, _, _, _, .lit _ _ _ _ _ hexp, hexpW, σ, _, hs, hc =>
      closedAt_eps hexp hexpW σ hs hc
  | _, _, _, _, _, .conv _ _ _ _ _ _ _ h _, hW, σ, _, hs, hc =>
      closedAt_eps h hW σ hs hc
  | _, _, _, _, _, .wk _ _ _ _ _ d c D, hW, σ, ρ, hs, hc => by
      obtain ⟨hs', hc', hck⟩ := wk_closed_step d hW.1 hs hc
      have ih := closedAt_eps D hW.2 σ hs' hc'
      rcases hck with ⟨hk, hcnt⟩ | ⟨hnk, hcnt⟩
      · rw [eps_wk_keep hk, hcnt]
        exact ETm.closedAt_lift (countKeep (ρ.take c)) 1 ih
      · rw [eps_wk_not_keep_of_ne hnk, ← hcnt]
        exact ih
  | _, _, _, _, _, .esub _ _ _ _ _ _ v j u D hget hv _, hW, σ, ρ, hs, hc => by
      simp only [TyP.eps]
      cases levelIsZero (σ u) with
      | true =>
          have ih := closedAt_eps D hW.1 σ
            (dispShape_insertDisp_drop v hget hs)
            (dispClosed_insertDisp_drop hc j)
          rwa [countKeep_insertDisp_drop] at ih
      | false =>
          have ihD := closedAt_eps D hW.1 σ
            (dispShape_insertDisp_keep v hget hs)
            (dispClosed_insertDisp_keep hc j)
          rw [countKeep_insertDisp_keep] at ihD
          have ihv := closedAt_eps hv hW.2 σ hs hc
          exact ETm.closedAt_inst (countKeep_take_le ρ j) ihv ihD
  | _, _, _, _, _, .lsub _ _ _ _ _ _ v j _ D hget hv hvT, hW, σ, ρ, hs, hc => by
      rw [lsub_eps_eq D hget hv hvT]
      have ihv := closedAt_eps hv hW.2.2 σ hs hc
      have ihD := closedAt_eps D hW.2.1 σ
        (dispShape_insertDisp_lsub v hW.1 hget hs (countKeep (ρ.take j)) (hv.eps σ ρ))
        (dispClosed_insertDisp_lsub hW.1 hc (countKeep (ρ.take j)) ihv)
      rwa [countKeep_insertDisp_lsub hW.1] at ihD
  | _, _, _, _, _, .linst _ _ _ _ _ _ ls _ _ D, hDW, σ, _, hs, hc =>
      closedAt_eps D hDW (fun l => σ (instLevel ls l)) (dispShape_of_instLvlsCtx ls hs) hc
  | _, _, _, _, _, .ewk _ _ _ _ _ _ _ D, hDW, σ, _, hs, hc =>
      closedAt_eps D hDW σ hs hc
  | _, _, _, _, _, .cctx _ _ _ _ _ _ _ _ D _, hDW, σ, _, hs, hc =>
      closedAt_eps D hDW σ (dispShape_cctx hs) hc

/-- Every closed derivation `D : TyP E n [] e T` satisfying `D.ClosedWf` erases at `ρ = []`
    to a closed erased term `ETm.ClosedAt 0 (D.eps σ [])`. -/
theorem closedAt_eps_nil {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) :
    ETm.ClosedAt 0 (D.eps σ []) :=
  closedAt_eps D hD σ .nil .nil

/-- The closed erasure `D.eps σ []` of any `D : TyP E n [] e T` with `D.ClosedWf` is
    fixed by `ETm.lift c k`. -/
theorem eps_nil_lift {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) (c k : Nat) :
    (D.eps σ []).lift c k = D.eps σ [] :=
  ETm.lift_closed0 (closedAt_eps_nil hD σ) c k

/-- Specialization of `eps_nil_lift` to `c = 0, k = 1`, discharging the `hlift` premise
    of `eps_deltaBodyInst` and `es_of_below_delta_table`. -/
theorem eps_nil_lift_zero {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) :
    (D.eps σ []).lift 0 1 = D.eps σ [] :=
  eps_nil_lift hD σ 0 1

/-- The closed erasure `D.eps σ []` of any `D : TyP E n [] e T` with `D.ClosedWf` is
    fixed by `ETm.inst j r`. -/
theorem eps_nil_inst {E : ResolvedEnv} {n : Nat} {e T : Expr Nat}
    {D : TyP E n [] e T} (hD : D.ClosedWf) (σ : Level → Level) (j : Nat) (r : ETm) :
    ETm.inst j r (D.eps σ []) = D.eps σ [] :=
  ETm.inst_closed0 (closedAt_eps_nil hD σ) j r

/-- For any enriched context `C : CtxP E n Γ` satisfying `C.ClosedWf`, its canonical
    disposition list `C.disp σ` satisfies `DispClosed (C.disp σ)`. -/
theorem dispClosed_of_ctxP (σ : Level → Level) {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (C : CtxP E n Γ) → C.ClosedWf → DispClosed (C.disp σ)
  | _, .nil _ _, _ => .nil
  | _, .assumption _ _ _ _ u hC _, hCW => by
      simp only [CtxP.disp]
      cases levelIsZero (σ u) with
      | true => exact .drop (dispClosed_of_ctxP σ hC hCW)
      | false => exact .keep (dispClosed_of_ctxP σ hC hCW)
  | _, .letBinding _ _ _ _ _ _ hC _ hv, hW =>
      .inline
        (closedAt_eps hv hW.2 σ (dispShape_of_ctxP σ hC) (dispClosed_of_ctxP σ hC hW.1))
        (dispClosed_of_ctxP σ hC hW.1)

/-- At `C.disp σ`, any `D : TyP E n Γ e T` with `D.ClosedWf` and `C.ClosedWf` erases to a term
    satisfying `ETm.ClosedAt (countKeep (C.disp σ))`. -/
theorem closedAt_eps_ctxP {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e T : Expr Nat}
    {C : CtxP E n Γ} (hCW : C.ClosedWf) {D : TyP E n Γ e T} (hDW : D.ClosedWf)
    (σ : Level → Level) :
    ETm.ClosedAt (countKeep (C.disp σ)) (D.eps σ (C.disp σ)) :=
  closedAt_eps D hDW σ (dispShape_of_ctxP σ C) (dispClosed_of_ctxP σ C hCW)

/-- Every plain closed typing `h : HasTyT E₁ n [] e T` unconditionally erases to a closed
    term `ETm.ClosedAt 0` at `ρ = []`. -/
theorem closedAt_enrichHasTyT_nil {E₁ E : ResolvedEnv} {n : Nat}
    (hcl : EnvClosed E) (hext : EnvExt E₁ E) (hm : MemberSortP E) (hlet : LetCtxConvP E n)
    {e T : Expr Nat} (h : HasTyT E₁ n [] e T) (σ : Level → Level) :
    ETm.ClosedAt 0 ((enrichHasTyT hcl hext hm hlet (.nil E n) h).eps σ []) :=
  closedAt_eps_nil (closedWf_enrichHasTyT hcl hext hm hlet (.nil E n) h) σ

/-! ## §3 Constant Rules (`deltaRule`), `TableWF` Combinators, and `CvP.delta` Table Discharge -/

/-- The bare nullary constant rule associated to a closed member body typing
    `D_b : TyP E a [] b T` at environment slot `r`. -/
def deltaRule (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    (D_b : TyP E a [] b T) : CRule where
  head := r
  nargs := fun _ => 0
  major := none
  rhs := fun ls _ => D_b.eps (instLevel ls) []

/-- `deltaRule r D_b` has `LvlEq`-congruent right-hand sides for **every** `D_b : TyP E a [] b T`. -/
theorem deltaRule_congr_rhs (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    (D_b : TyP E a [] b T) {ls₁ ls₂ ms₁ ms₂ : List Level}
    (hls : eqNList ls₁ ls₂) (_hms : eqNList ms₁ ms₂) :
    LvlEq ((deltaRule r D_b).rhs ls₁ ms₁) ((deltaRule r D_b).rhs ls₂ ms₂) :=
  lvlEq_eps_instLevel_nil D_b hls

/-- Under `D_b.ClosedWf`, `deltaRule r D_b` has closed right-hand sides (`ETm.ClosedAt 0`). -/
theorem deltaRule_closed (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {D_b : TyP E a [] b T} (hDb : D_b.ClosedWf) (ls ms : List Level) :
    ETm.ClosedAt 0 ((deltaRule r D_b).rhs ls ms) :=
  closedAt_eps_nil hDb (instLevel ls)

/-- Extending a `TableCongr` table by `deltaRule r D_b` preserves `TableCongr`. -/
theorem tableCongr_cons_deltaRule {tbl : List CRule} (hT : TableCongr tbl)
    (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat} (D_b : TyP E a [] b T) :
    TableCongr (deltaRule r D_b :: tbl) where
  rhs := by
    intro ρ hρ ls₁ ls₂ ms₁ ms₂ hls hms
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · exact deltaRule_congr_rhs r D_b hls hms
    · exact hT.rhs ρ hρ' hls hms
  nargs := by
    intro ρ hρ ls₁ ls₂ hls
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · rfl
    · exact hT.nargs ρ hρ' hls
  marity := by
    intro ρ hρ d m hm ls₁ ls₂ hls
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · cases hm
    · exact hT.marity ρ hρ' hm hls

/-- Extending a `TableWF` table by `deltaRule r D_b` preserves `TableWF` whenever
    `D_b.ClosedWf` holds and `r` is fresh with respect to heads and major constructors in `tbl`. -/
theorem tableWF_cons_deltaRule {tbl : List CRule} (hW : TableWF tbl)
    (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {D_b : TyP E a [] b T} (hDb : D_b.ClosedWf)
    (hfresh_head : ∀ σ ∈ tbl, σ.head ≠ r)
    (hfresh_maj : ∀ ρ ∈ tbl, ∀ {d : Nat} {m : List Level → Nat},
      ρ.major = some (d, m) → r ≠ d) :
    TableWF (deltaRule r D_b :: tbl) where
  congr := tableCongr_cons_deltaRule hW.congr r D_b
  closed := by
    intro ρ hρ ls ms
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · exact deltaRule_closed r hDb ls ms
    · exact hW.closed ρ hρ' ls ms
  rigid := by
    intro ρ hρ d m hm σ hσ
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · cases hm
    · rcases List.mem_cons.mp hσ with rfl | hσ'
      · exact hfresh_maj ρ hρ' hm
      · exact hW.rigid ρ hρ' hm σ hσ'
  bare_unique := by
    intro ρ hρ hm σ hσ hhead
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · rcases List.mem_cons.mp hσ with rfl | hσ'
      · rfl
      · exact absurd hhead (hfresh_head σ hσ')
    · rcases List.mem_cons.mp hσ with rfl | hσ'
      · exact absurd hhead.symm (hfresh_head ρ hρ')
      · exact hW.bare_unique ρ hρ' hm σ hσ' hhead
  ctor_disjoint := by
    intro ρ hρ σ hσ hhead d e m n hm_ρ hm_σ
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · cases hm_ρ
    · rcases List.mem_cons.mp hσ with rfl | hσ'
      · cases hm_σ
      · exact hW.ctor_disjoint ρ hρ' σ hσ' hhead hm_ρ hm_σ
  bare_nullary := by
    intro ρ hρ hm ls
    rcases List.mem_cons.mp hρ with rfl | hρ'
    · rfl
    · exact hW.bare_nullary ρ hρ' hm ls

/-- Any singleton table `[deltaRule r D_b]` with `D_b.ClosedWf` satisfies `TableWF`. -/
theorem tableWF_singleton_deltaRule (r : Nat) {E : ResolvedEnv} {a : Nat} {b T : Expr Nat}
    {D_b : TyP E a [] b T} (hDb : D_b.ClosedWf) :
    TableWF [deltaRule r D_b] :=
  tableWF_cons_deltaRule tableWF_nil r hDb (fun _ h => nomatch h) (fun _ h => nomatch h)

/-- `eps_deltaBodyInst` with the `hlift` premise automatically discharged by `D_b.ClosedWf`. -/
theorem eps_deltaBodyInst_closed {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E)
    {r : Nat} {ls : List Level} {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (hlen : ls.length = m.arity) (hwf : levelsBounded n ls = true)
    (Γ : LCtx) {D_b : TyP E m.arity [] b m.mtype} (hDb : D_b.ClosedWf)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ) :
    (deltaBodyInst hE hres hbody hlen hwf Γ D_b).eps σ ρ =
      D_b.eps (fun l => σ (instLevel ls l)) [] :=
  eps_deltaBodyInst hE hres hbody hlen hwf Γ D_b σ ρ hρ
    (eps_nil_lift_zero hDb (fun l => σ (instLevel ls l)))

/-- `es_of_below_delta_table` with the `hlift` premise automatically discharged by `D_b.ClosedWf`. -/
theorem es_of_below_delta_table_closed (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    {crule : CRule} (hcrule : crule ∈ tbl) (hhead : crule.head = r)
    (hmaj : crule.major = none) (hnargs : crule.nargs (ls.map σ) = 0)
    (hrhs_eq : crule.rhs (ls.map σ) [] = D_b.eps (fun l => σ (instLevel ls l)) [])
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) :=
  es_of_below_delta_table Aw tbl hE hres hbody htrp hlen hwf hb dl dr D_b hDb_wt σ ρ hρ hu
    (eps_nil_lift_zero hDb_cl (fun l => σ (instLevel ls l)))
    hcrule hhead hmaj hnargs hrhs_eq Bel

/-- `ES` for `CvP.delta` when `deltaRule r D_b ∈ tbl` and `D_b.ClosedWf` holds, allowing
    `LvlEq` between `D_b.eps (instLevel (ls.map σ)) []` and `D_b.eps (fun l => σ (instLevel ls l)) []`. -/
theorem es_of_below_delta_crule (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hmem : deltaRule r D_b ∈ tbl)
    (hlvl : LvlEq (D_b.eps (instLevel (ls.map σ)) [])
      (D_b.eps (fun l => σ (instLevel ls l)) []))
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  have hcl := delta_body_cl Aw tbl hE hres hbody htrp hlen hwf hb dl dr D_b hDb_wt σ ρ hρ Bel
  unfold CL at hcl
  rw [eps_deltaBodyInst_closed hE hres hbody hlen hwf Γ hDb_cl σ ρ hρ] at hcl
  have hcroot : CRoot tbl (.const r (ls.map σ)) ((deltaRule r D_b).rhs (ls.map σ) []) :=
    CRoot.bare (tbl := tbl) hmem rfl (ls.map σ) [] rfl
  exact es_of_below_delta_rel Aw tbl hres hbody htrp hlen hwf hb dl dr σ ρ hρ hu Bel
    (.inl (.cr hcroot)) ((ConvMod.eqv hlvl).trans hcl)

/-- At `σ = id`, `deltaRule r D_b ∈ tbl` and `D_b.ClosedWf` discharge `ES` for `CvP.delta`
    with zero `hlift` and zero `hlvl` hypotheses. -/
theorem es_of_below_delta_crule_id (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (ρ : List Disp) (hρ : DispFor id E n Γ ρ)
    (hu : levelIsZero (id hb.reg.1) = false)
    (hmem : deltaRule r D_b ∈ tbl)
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl id ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) := by
  refine es_of_below_delta_crule Aw tbl hE hres hbody htrp hlen hwf hb dl dr
    D_b hDb_wt hDb_cl id ρ hρ hu hmem ?_ Bel
  rw [List.map_id]
  exact LvlEq.rfl' _

/-- Level homomorphisms (`id` and compositions with `instLevel`), commuting with
    `.zero`, `.succ`, `.max`, and `.imax`. -/
structure LevelHom (σ : Level → Level) : Prop where
  map_zero : σ .zero = .zero
  map_succ : ∀ l, σ (.succ l) = .succ (σ l)
  map_max : ∀ a b, σ (.max a b) = .max (σ a) (σ b)
  map_imax : ∀ a b, σ (.imax a b) = .imax (σ a) (σ b)

theorem levelHom_id : LevelHom id where
  map_zero := rfl
  map_succ := fun _ => rfl
  map_max := fun _ _ => rfl
  map_imax := fun _ _ => rfl

theorem LevelHom.linst {σ : Level → Level} (hσ : LevelHom σ) (ms : List Level) :
    LevelHom (fun l => σ (instLevel ms l)) where
  map_zero := hσ.map_zero
  map_succ := fun l => hσ.map_succ (instLevel ms l)
  map_max := fun a b => hσ.map_max (instLevel ms a) (instLevel ms b)
  map_imax := fun a b => hσ.map_imax (instLevel ms a) (instLevel ms b)

theorem getD_map_of_lt (σ : Level → Level) :
    (ls : List Level) → (i : Nat) → i < ls.length → (d : Level) →
      ((ls.map σ)[i]?).getD d = σ ((ls[i]?).getD d)
  | [], _, hi, _ => nomatch hi
  | _ :: _, 0, _, _ => by
      simp only [List.map_cons, List.getElem?_cons_zero, Option.getD_some]
  | _ :: ls, i + 1, hi, d => by
      simp only [List.map_cons, List.getElem?_cons_succ]
      exact getD_map_of_lt σ ls i (Nat.lt_of_succ_lt_succ hi) d

/-- For any `LevelHom σ` and level `l` bounded by `ls.length`,
    `instLevel (ls.map σ) l = σ (instLevel ls l)`. -/
theorem instLevel_map_of_levelHom {σ : Level → Level} (hσ : LevelHom σ) (ls : List Level) :
    (l : Level) → levelBounded ls.length l = true →
      instLevel (ls.map σ) l = σ (instLevel ls l)
  | .zero, _ => hσ.map_zero.symm
  | .succ l, hl => by
      rw [instLevel_succ, instLevel_succ, hσ.map_succ,
        instLevel_map_of_levelHom hσ ls l hl]
  | .max a b, hl => by
      rw [instLevel_max, instLevel_max, hσ.map_max,
        instLevel_map_of_levelHom hσ ls a (boolAnd_left hl),
        instLevel_map_of_levelHom hσ ls b (boolAnd_right hl)]
  | .imax a b, hl => by
      rw [instLevel_imax, instLevel_imax, hσ.map_imax,
        instLevel_map_of_levelHom hσ ls a (boolAnd_left hl),
        instLevel_map_of_levelHom hσ ls b (boolAnd_right hl)]
  | .param i, hl =>
      getD_map_of_lt σ ls i (of_decide_eq_true hl) (.param i)

/-- `ES` for `CvP.delta` when `deltaRule r D_b ∈ tbl`, `D_b.ClosedWf` holds, and
    `instLevel (ls.map σ)` agrees up to `eqN` with `fun l => σ (instLevel ls l)`. -/
theorem es_of_below_delta_crule_eqN (Aw : Nat → Nat) (tbl : List CRule)
    {E : ResolvedEnv} {n : Nat} (hE : EnvWfT E) {Γ : LCtx} {r : Nat} {ls : List Level}
    {m : CheckedMember} {b : Expr Nat}
    (hres : E.members r = some m) (hbody : m.body = some b)
    (htrp : transparent m.mclass = true) (hlen : ls.length = m.arity)
    (hwf : levelsBounded n ls = true)
    (hb : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (dl : TyP E n Γ (.const r ls) (instantiateLevels ls m.mtype))
    (dr : TyP E n Γ (instantiateLevels ls b) (instantiateLevels ls m.mtype))
    (D_b : TyP E m.arity [] b m.mtype) (hDb_wt : D_b.wt Aw ≤ Aw r) (hDb_cl : D_b.ClosedWf)
    (σ : Level → Level) (ρ : List Disp) (hρ : DispFor σ E n Γ ρ)
    (hu : levelIsZero (σ hb.reg.1) = false)
    (hmem : deltaRule r D_b ∈ tbl)
    (hσ : ∀ l, eqN (instLevel (ls.map σ) l) (σ (instLevel ls l)))
    (Bel : Below Aw tbl
      (cvMeas Aw (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr))) :
    ES tbl σ ρ (CvP.delta E n Γ r ls m b hres hbody htrp hlen hwf hb dl dr) :=
  es_of_below_delta_crule Aw tbl hE hres hbody htrp hlen hwf hb dl dr
    D_b hDb_wt hDb_cl σ ρ hρ hu hmem (lvlEq_eps D_b hσ .nil) Bel

end Rcic.Syn
