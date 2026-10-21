import rcic.RcicSynSRBetaZetaStepWNoInline
import rcic.RcicSynLetTrace

/-!
# The out-of-range `wk` corner (`Γ.length < c`): measurement infrastructure

cc's 04:15Z brief, item (2): measure whether a demanded query can reach the
out-of-range corner of `StepSuppliersW.es_wk_keep_reframe` at all
(Demand-reachability from a root); if unreachable, prove that and close the
field. The row fires only when, at a demanded `wk`-keep query with
`Γ.length < c`, BOTH `ρ[c]? = some .keep` AND
`wkInnerDisp ρ c ≠ removeAt ρ c` hold.

This module lands the base layers of the vacuity argument:

* §1 `routedDisp_length_ge` — every routed display is at least as long as
  its context (`Δ.length ≤ ρ.length`).
* §2 `wk_noOp_outOfRange` — a no-op `wk` edge (`ρ.length ≤ c`) at a
  demanded query forces `Γ.length < c`, so the demand's `AssumpPref`-pinned
  `AssumptionPrefix Γ c` covers ALL of `Γ`: a no-op issuer's inner context
  is all assumptions.
* §3 the root case — a demanded `wk` query whose display is the canonical
  `S.can σ` has an exact-length display, so `ρ[c]? = none` at every
  out-of-range cutoff: the corner cannot be reached at a root.

Remaining (the issued case, roadmap for the next slice): the display-length
accounting through every `Issues` row (only a no-op `wk_es` edge can grow
`ρ.length − Δ.length`), the stale-stack shape (no `.inline` strictly below
a `.keep` in the padding zone: a let-carrying no-op issuer blocks every
later no-op above it, so its stale is topmost), and the ancestor-context
let-survival (`esub` only substitutes `.assumption` entries, so the
corner's own `d` survives into every issuer context and blocks all no-ops
above it when it is a let — forcing `ρ.length = Δ.length`, killing `hk`).
§5 is the reduction engine those families feed: `wkInnerDisp ρ c` equals
`removeAt ρ c` whenever every inline below `c` is `ClosedAt` its unlift
slot (`countKeep [j, c)`); the per-family work is to derive that closedness
from `eps_support` (`RcicERScope2`) + the REL/stale-stack invariants.
`closure_claim = 0`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 routed displays are at least context-length -/

theorem removeAt_length_ge (ρ : List Disp) (c : Nat) :
    ρ.length - 1 ≤ (removeAt ρ c).length := by
  induction ρ generalizing c with
  | nil => simp [removeAt]
  | cons d ρ ih =>
      cases c with
      | zero => simp [removeAt]
      | succ c =>
          have h := ih c
          simp only [removeAt, List.length_cons]
          omega

theorem removeAt_length_le (ρ : List Disp) (c : Nat) :
    (removeAt ρ c).length ≤ ρ.length := by
  induction ρ generalizing c with
  | nil => simp [removeAt]
  | cons d ρ ih =>
      cases c with
      | zero => simp [removeAt]
      | succ c =>
          have h := ih c
          simp only [removeAt, List.length_cons]
          omega

/-- Every routed display is at least as long as its context. -/
theorem routedDisp_length_ge {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : RoutedDisp σ E n Γ ρ) : Γ.length ≤ ρ.length := by
  induction h with
  | @canon σ _ _ Γ C =>
      rw [ctxP_disp_length C]
      omega
  | @assumption σ _ _ _ _ _ _ _ _ ih =>
      have h := ih
      simp only [List.length_cons]
      omega
  | letDrop _ _ _ _ ih =>
      simp only [List.length_cons]
      omega
  | @letInline σ _ _ _ _ _ _ _ _ _ ih =>
      simp only [List.length_cons]
      omega
  | @wk σ _ _ Γ ρ d c _ ih =>
      have h1 := insertAt_length d c Γ
      have h2 := removeAt_length_ge ρ c
      omega
  | @esub σ _ _ Γ ρ t v j u _ _ _ ih =>
      have h0 : Γ.length ≤ (substRemove v j Γ).length + 1 := by
        rw [substRemove_length]
        split <;> omega
      have h2 := insertDisp_length (binderDisp (levelIsZero (σ u))) j ρ
      omega
  | @linst σ _ _ _ Γ ρ ls _ _ _ ih =>
      have hmaplen : (instLvlsCtx ls Γ).length = Γ.length := by
        unfold instLvlsCtx
        simp
      omega
  | ewk _ _ ih => exact ih
  | cctx _ _ ih =>
      simp only [List.length_cons] at ih ⊢
      omega

/-! ## §2 no-op `wk` edges at demanded queries -/

/-- A no-op `wk` edge at a demanded query has an out-of-range cutoff in the
    strong sense: routing pins `insertAt d c Γ`-length onto the display, the
    no-op (`ρ.length ≤ c`) then forces `Γ.length < c`, and the demand's
    `AssumpPref`-pinned `AssumptionPrefix Γ c` covers ALL of `Γ`. The no-op
    issuer's inner context is therefore all assumptions. -/
theorem wk_noOp_outOfRange {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {d : LocalDecl} {c : Nat} {h : CvP E n Γ a b T}
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx} {S : ScopedCtx Eₐ E₀ n₀ Γ₀}
    {σ : Level → Level} {ρ : List Disp}
    (hq : Demand (.es (CvP.wk E n Γ a b T d c h) S σ ρ))
    (hnoOp : ρ.length ≤ c) : Γ.length < c ∧ AssumptionPrefix Γ c := by
  have hap : (CvP.wk E n Γ a b T d c h).AssumpPref := Demand.ap hq
  have hap' : AssumptionPrefix Γ c ∧ h.AssumpPref := hap
  have hr : RoutedDisp σ E n (insertAt d c Γ) ρ := Demand.routed hq
  have h1 := routedDisp_length_ge hr
  have h2 := insertAt_length d c Γ
  exact ⟨by omega, hap'.1⟩

/-! ## §3 the root case: canonical displays are exact-length -/

/-- The canonical display of a scope has exactly its context's length. -/
theorem scopedCtx_can_length {Eₐ : ResolvedEnv} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) :
    (S.can σ).length = Γ.length := ctxP_disp_length _

/-- A canonical display at a `wk` node's own (extended) context has no
    entry at any out-of-range cutoff — the corner's `hk` fails at every
    root (`Demand.rootEs` instantiates the scope at the derivation's
    context `insertAt d c Γ`). -/
theorem wk_canonicalDisp_notKeep {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {d : LocalDecl} {c : Nat}
    (S : ScopedCtx Eₐ E n (insertAt d c Γ)) (σ : Level → Level)
    (hc : Γ.length < c) : (S.can σ)[c]? ≠ some Disp.keep := by
  have h3 : (S.can σ)[c]? = none := by
    rw [List.getElem?_eq_none_iff, scopedCtx_can_length, insertAt_length]
    omega
  rw [h3]
  simp

/-- At a root, the corner row's premise bundle is empty: with the canonical
    display there is no `.keep` at the out-of-range cutoff, so
    `wkInnerDisp` takes the definitional `removeAt` arm. -/
theorem wkInnerDisp_eq_removeAt_canonical {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
    {d : LocalDecl} {c : Nat}
    (S : ScopedCtx Eₐ E n (insertAt d c Γ)) (σ : Level → Level)
    (hc : Γ.length < c) :
    wkInnerDisp (S.can σ) c = removeAt (S.can σ) c := by
  have h3 : (S.can σ)[c]? = none := by
    rw [List.getElem?_eq_none_iff, scopedCtx_can_length, insertAt_length]
    omega
  simp only [wkInnerDisp, h3]

/-! ## §4 the frame arithmetic: `resolve` slots vs `countKeep` prefixes -/

/-- `resolve` against a `.keep` at position `j` yields the de Bruijn index
    that counts exactly the keeps strictly below `j` — the slot of a value
    erasure at a keep is the keep-prefix count of its own position. -/
theorem resolve_keep_slot {ρ : List Disp} {j : Nat} (h : ρ[j]? = some Disp.keep) :
    resolve ρ j = .bvar (countKeep (List.take j ρ)) := by
  induction ρ generalizing j with
  | nil => simp at h
  | cons d ρ ih =>
      cases j with
      | zero =>
          cases d with
          | keep => rfl
          | drop => simp at h
          | inline v => simp at h
      | succ j =>
          have hj : ρ[j]? = some Disp.keep := by
            simpa only [List.getElem?_cons_succ] using h
          have ihj := ih hj
          cases d with
          | keep =>
              show (resolve ρ j).lift 0 1 = .bvar (countKeep (List.take j ρ) + 1)
              rw [ihj, ETm.lift]
              simp
          | drop =>
              show resolve ρ j = .bvar (countKeep (List.take j ρ))
              exact ihj
          | inline v =>
              show resolve ρ j = .bvar (countKeep (List.take j ρ))
              exact ihj

/-- The walk's reframe index strictly overshoots the slot of a keep-erased
    value whenever the value's own position is strictly below the walk's
    cutoff: the keep at `j` itself is counted in `countKeep (take c ρ)` but
    not in the slot produced at `j`. -/
theorem countKeep_take_mono_keep {ρ : List Disp} {j c : Nat}
    (hj : ρ[j]? = some Disp.keep) (hjc : j < c) :
    countKeep (List.take j ρ) < countKeep (List.take c ρ) := by
  induction ρ generalizing j c with
  | nil => simp at hj
  | cons d ρ ih =>
      cases j with
      | zero =>
          cases c with
          | zero => omega
          | succ c =>
              cases d with
              | keep =>
                  show countKeep [] < countKeep (Disp.keep :: List.take c ρ)
                  simp only [countKeep]
                  omega
              | drop => simp at hj
              | inline v => simp at hj
      | succ j =>
          have hj' : ρ[j]? = some Disp.keep := by
            simpa only [List.getElem?_cons_succ] using hj
          cases c with
          | zero => omega
          | succ c =>
              have hijc : j < c := by omega
              have hlt := ih hj' hijc
              cases d with
              | keep =>
                  show countKeep (List.take j ρ) + 1 < countKeep (List.take c ρ) + 1
                  omega
              | drop =>
                  show countKeep (List.take j ρ) < countKeep (List.take c ρ)
                  exact hlt
              | inline v =>
                  show countKeep (List.take j ρ) < countKeep (List.take c ρ)
                  exact hlt

/-! ## §5 the reframe fixpoint: per-inline closedness forces `wkInnerDisp = removeAt` -/

/-- β-style instantiate at `★` is the identity below the slot: `inst m ★ v`
    replaces slot `m` by `★` and shifts everything above it down, so it can
    only differ from `v` at indices `≥ m` (at each binder depth). -/
theorem inst_star_eq_of_closedAt (m : Nat) (v : ETm) (h : ETm.ClosedAt m v) :
    ETm.inst m .star v = v := by
  induction v generalizing m with
  | bvar i =>
      have him : i < m := h
      show (if i = m then ETm.star else if m < i then ETm.bvar (i - 1) else ETm.bvar i)
        = ETm.bvar i
      rw [if_neg (by omega), if_neg (by omega)]
  | star => rfl
  | sort l => rfl
  | const c ls => rfl
  | app f a ihf iha =>
      show ETm.app (ETm.inst m ETm.star f) (ETm.inst m ETm.star a) = ETm.app f a
      rw [ihf m h.1, iha m h.2]
  | lam b ih =>
      show ETm.lam (ETm.inst (m + 1) (ETm.lift 0 1 ETm.star) b) = ETm.lam b
      rw [show ETm.lift 0 1 (ETm.star : ETm) = ETm.star from rfl, ih (m + 1) h]
  | pi a b iha ihb =>
      show ETm.pi (ETm.inst m ETm.star a) (ETm.inst (m + 1) (ETm.lift 0 1 ETm.star) b)
        = ETm.pi a b
      rw [show ETm.lift 0 1 (ETm.star : ETm) = ETm.star from rfl, iha m h.1, ihb (m + 1) h.2]

/-- **POINTWISE REDUCTION of the corner (roadmap (i)/(iv) engine).** The
    walk `wkInnerGo r c ρ` unlifts the inline at position `j < c` exactly at
    the slot `r − countKeep (take j ρ)` (the keeps in `[j, c)` — the inserted
    keep's own slot in that value's frame); if every inline below `c` is
    `ClosedAt` its slot, the whole pass is `removeAt ρ c`. -/
theorem wkInnerGo_eq_removeAt_of_closedAt :
    ∀ (c : Nat) (ρ : List Disp) (r : Nat), r = countKeep (List.take c ρ) →
      (∀ j v, j < c → ρ[j]? = some (Disp.inline v) →
        ETm.ClosedAt (r - countKeep (List.take j ρ)) v) →
      wkInnerGo r c ρ = removeAt ρ c := by
  intro c
  induction c with
  | zero =>
      intro ρ r _ _
      cases ρ <;> rfl
  | succ c ih =>
      intro ρ r hr hf
      cases ρ with
      | nil => rfl
      | cons d t =>
          cases d with
          | keep =>
              have h1 : countKeep (List.take (c + 1) (Disp.keep :: t))
                  = countKeep (List.take c t) + 1 := rfl
              have hr' : r - 1 = countKeep (List.take c t) := by omega
              have htail : ∀ j v, j < c → t[j]? = some (Disp.inline v) →
                  ETm.ClosedAt (r - 1 - countKeep (List.take j t)) v := by
                intro j v hj hv
                have hj' := hf (j + 1) v (Nat.succ_lt_succ hj)
                  (by simpa only [List.getElem?_cons_succ] using hv)
                have hsplit : countKeep (List.take (j + 1) (Disp.keep :: t))
                    = countKeep (List.take j t) + 1 := rfl
                rw [show r - 1 - countKeep (List.take j t)
                    = r - countKeep (List.take (j + 1) (Disp.keep :: t)) from by
                      rw [hsplit]; omega]
                exact hj'
              show Disp.keep :: wkInnerGo (r - 1) c t = Disp.keep :: removeAt t c
              rw [ih t (r - 1) hr' htail]
          | drop =>
              have h1 : countKeep (List.take (c + 1) (Disp.drop :: t))
                  = countKeep (List.take c t) := rfl
              have hr' : r = countKeep (List.take c t) := by omega
              have htail : ∀ j v, j < c → t[j]? = some (Disp.inline v) →
                  ETm.ClosedAt (r - countKeep (List.take j t)) v := by
                intro j v hj hv
                have hj' := hf (j + 1) v (Nat.succ_lt_succ hj)
                  (by simpa only [List.getElem?_cons_succ] using hv)
                have hsplit : countKeep (List.take (j + 1) (Disp.drop :: t))
                    = countKeep (List.take j t) := rfl
                rw [show r - countKeep (List.take j t)
                    = r - countKeep (List.take (j + 1) (Disp.drop :: t)) from by
                      rw [hsplit]]
                exact hj'
              show Disp.drop :: wkInnerGo r c t = Disp.drop :: removeAt t c
              rw [ih t r hr' htail]
          | inline v =>
              have h00 : countKeep (List.take 0 (Disp.inline v :: t)) = 0 := rfl
              have hcl : ETm.ClosedAt r v := by
                have h0 := hf 0 v (Nat.zero_lt_succ c) (by simp)
                rw [h00, Nat.sub_zero] at h0
                exact h0
              have h1 : countKeep (List.take (c + 1) (Disp.inline v :: t))
                  = countKeep (List.take c t) := rfl
              have hr' : r = countKeep (List.take c t) := by omega
              have htail : ∀ j w, j < c → t[j]? = some (Disp.inline w) →
                  ETm.ClosedAt (r - countKeep (List.take j t)) w := by
                intro j w hj hv
                have hj' := hf (j + 1) w (Nat.succ_lt_succ hj)
                  (by simpa only [List.getElem?_cons_succ] using hv)
                have hsplit : countKeep (List.take (j + 1) (Disp.inline v :: t))
                    = countKeep (List.take j t) := rfl
                rw [show r - countKeep (List.take j t)
                    = r - countKeep (List.take (j + 1) (Disp.inline v :: t)) from by
                      rw [hsplit]]
                exact hj'
              show Disp.inline (ETm.inst r .star v) :: wkInnerGo r c t
                = Disp.inline v :: removeAt t c
              rw [inst_star_eq_of_closedAt r v hcl]
              rw [ih t r hr' htail]

/-- The corner's per-inline criterion, packaged at `wkInnerDisp`: if every
    inline below the cutoff is closed below its unlift slot, the reframe is
    a no-op and the closer reads `removeAt` even OUT of range. -/
theorem wkInnerDisp_eq_removeAt_of_closedAt {ρ : List Disp} {c : Nat}
    (h : ∀ j v, j < c → ρ[j]? = some (Disp.inline v) →
      ETm.ClosedAt (countKeep (List.take c ρ) - countKeep (List.take j ρ)) v) :
    wkInnerDisp ρ c = removeAt ρ c := by
  unfold wkInnerDisp
  split
  · rename_i hk
    exact wkInnerGo_eq_removeAt_of_closedAt c ρ _ rfl h
  · rfl

/-! ## §6 the display-length accounting — only out-of-range `wk` grows the surplus

Every `RoutedDisp` row preserves `ρ.length − Γ.length` except `wk`, whose
`removeAt` shrinks the display exactly when `c < ρ.length`. At `c ≥ ρ.length`
the remove is a no-op while the premise context (`insertAt d c Γ`, which
clamps the appended decl to the tail) is one longer — surplus `+1`, the stale
stack's only birth. `wkOOR` counts those rows; the accounting theorem pins
`ρ.length = Γ.length + wkOOR`. -/

theorem removeAt_eq_of_ge : ∀ (ρ : List Disp) {c : Nat},
    ρ.length ≤ c → removeAt ρ c = ρ
  | [], _, _ => rfl
  | _ :: ρ, 0, h => absurd h (Nat.not_succ_le_zero _)
  | d :: ρ, c + 1, h => by
      simp only [List.length_cons] at h
      exact congrArg (d :: ·) (removeAt_eq_of_ge ρ (Nat.le_of_succ_le_succ h))

theorem removeAt_length_of_lt : ∀ (ρ : List Disp) {c : Nat},
    c < ρ.length → (removeAt ρ c).length = ρ.length - 1
  | _ :: ρ, 0, _ => rfl
  | d :: ρ, c + 1, h => by
      simp only [List.length_cons] at h
      simp only [removeAt, List.length_cons]
      have ih := removeAt_length_of_lt ρ (Nat.lt_of_succ_lt_succ h)
      omega

/-- The surplus witness: a routed display longer than its context descends
    from an out-of-range `wk` row (`removeAt` a no-op at `c ≥ ρ.length`, the
    `insertAt` premise one slot longer). Every other row preserves the
    surplus on both sides, so this `wk` is the only birth of stale entries. -/
theorem routedDisp_wk_witness {σ : Level → Level} {E : ResolvedEnv} {n : Nat}
    {Γ : LCtx} {ρ : List Disp} (h : RoutedDisp σ E n Γ ρ) :
    Γ.length < ρ.length →
      ∃ (σ' : Level → Level) (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx)
        (ρ' : List Disp) (d : LocalDecl) (c : Nat),
        ρ'.length ≤ c ∧ Nonempty (RoutedDisp σ' E' n' (insertAt d c Γ') ρ') := by
  induction h with
  | canon C =>
      intro hl
      rw [ctxP_disp_length C] at hl
      exact absurd hl (Nat.lt_irrefl _)
  | assumption h _ ih =>
      intro hl
      simp only [List.length_cons] at hl
      exact ih (by omega)
  | letDrop h _ _ _ ih =>
      intro hl
      simp only [List.length_cons] at hl
      exact ih (by omega)
  | letInline h _ _ ih =>
      intro hl
      simp only [List.length_cons] at hl
      exact ih (by omega)
  | @wk _ _ _ Γ' ρ' d c h ih =>
      intro hl
      by_cases hc : ρ'.length ≤ c
      · exact ⟨_, _, _, Γ', ρ', d, c, hc, ⟨h⟩⟩
      · rw [removeAt_length_of_lt ρ' (Nat.lt_of_not_ge hc)] at hl
        rw [insertAt_length] at ih
        exact ih (by omega)
  | @esub _ _ _ Γ ρ' _ _ j _ hget _ _ h ih =>
      intro hl
      have hj := getElem?_lt_length hget
      rw [insertDisp_length] at hl
      rw [substRemove_length_lt hj] at ih
      exact ih (by omega)
  | linst _ _ _ h ih =>
      intro hl
      exact ih (by simpa only [instLvlsCtx, List.length_map] using hl)
  | ewk _ _ ih => exact ih
  | cctx _ _ ih =>
      intro hl
      exact ih (by simpa only [List.length_cons] using hl)

/-- Tail membership implies membership. -/
theorem mem_of_list_tail {α : Type _} {a : α} {l : List α} (h : a ∈ l.tail) : a ∈ l := by
  cases l with
  | nil => exact h
  | cons x xs => exact List.mem_cons_of_mem _ h

/-! ## §7 ancestor let-survival on the issue chain

The stale-stack blocking argument needs: a `.letBinding` entry in an issued
`.es` site's context at a non-head position (`Γ.tail`) survives into the
issuer's context. `esub` removes only `.assumption` entries (`hget`), `wk`'s
`insertAt` and `linst`'s `instLvlsCtx` rename the stored fields but re-kind
every entry (`liftDecl` / `instDecl` / `instLvlsDecl` map `.letBinding` to
`.letBinding`), and binder rows cons their own decl at index 0 — so a let at
index `≥ 1` is never the entry a row consumes. The `letE` binder rows are the
only escape: the issued `.letBinding` at index 0 IS their consed decl — hence
the tail premise. -/

/-- `insertAt` renames but never drops entries: a `.letBinding` member of `Γ`
    is a `.letBinding` member of `insertAt d c Γ` (its stored fields lift when
    it sits at or above the insertion point). -/
theorem letBinding_mem_insertAt (d : LocalDecl) (c : Nat) {A v : Expr Nat}
    {Γ : LCtx} (hm : LocalDecl.letBinding A v ∈ Γ) :
    ∃ A' v', LocalDecl.letBinding A' v' ∈ insertAt d c Γ := by
  induction c generalizing Γ with
  | zero => exact ⟨A, v, List.mem_cons_of_mem _ hm⟩
  | succ c ih =>
      cases Γ with
      | nil => exact absurd hm (List.not_mem_nil _)
      | cons x Γ =>
          rw [insertAt_succ_cons]
          cases hm with
          | head => exact ⟨_, _, List.mem_cons_self _ _⟩
          | tail _ htl =>
              obtain ⟨A', v', h⟩ := ih htl
              exact ⟨A', v', List.mem_cons_of_mem _ h⟩

/-- `substRemove` removes only index `j`; with `j` an `.assumption` (`hget`),
    every `.letBinding` member survives (instDecl'd when it sits below `j`). -/
theorem letBinding_mem_substRemove {v : Expr Nat} {j : Nat} {Γ : LCtx}
    {t : Expr Nat} (hget : Γ[j]? = some (.assumption t)) {A w : Expr Nat}
    (hm : LocalDecl.letBinding A w ∈ Γ) :
    ∃ A' w', LocalDecl.letBinding A' w' ∈ substRemove v j Γ := by
  induction j generalizing Γ with
  | zero =>
      cases Γ with
      | nil => simp at hget
      | cons x Γ =>
          simp only [List.getElem?_cons_zero] at hget
          cases hget
          cases hm with
          | tail _ htl => exact ⟨_, _, htl⟩
  | succ j ih =>
      cases Γ with
      | nil => simp at hget
      | cons x Γ =>
          rw [substRemove_succ_cons]
          simp only [List.getElem?_cons_succ] at hget
          cases hm with
          | head => exact ⟨_, _, List.mem_cons_self _ _⟩
          | tail _ htl =>
              obtain ⟨A', w', h⟩ := ih hget htl
              exact ⟨A', w', List.mem_cons_of_mem _ h⟩

/-- `instLvlsCtx` maps every entry through `instLvlsDecl`, which preserves
    `.letBinding`. -/
theorem letBinding_mem_instLvlsCtx (ls : List Level) {A v : Expr Nat} {Γ : LCtx}
    (hm : LocalDecl.letBinding A v ∈ Γ) :
    ∃ A' v', LocalDecl.letBinding A' v' ∈ instLvlsCtx ls Γ := by
  induction Γ with
  | nil => exact absurd hm (List.not_mem_nil _)
  | cons x Γ ih =>
      rw [instLvlsCtx_cons]
      cases hm with
      | head => exact ⟨_, _, List.mem_cons_self _ _⟩
      | tail _ htl =>
          obtain ⟨A', v', h⟩ := ih htl
          exact ⟨A', v', List.mem_cons_of_mem _ h⟩

/-- **Ancestor let-survival (one step).** A `.letBinding` member of an issued
    `.es` site's context tail survives into the issuer's site context: no
    `Issues` row reaching an `.es` removes or re-kinds a non-head let entry.
    The only escape is the `letE` binder rows' consed decl, which sits at
    index 0 — excluded by the `.tail` premise. -/
theorem issues_letTail {Eₐ : ResolvedEnv} {q : P2Query Eₐ}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {h : CvP E n Γ a b T} {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (e : Issues q (.es h S σ ρ)) {A v : Expr Nat}
    (hm : LocalDecl.letBinding A v ∈ Γ.tail) :
    ∃ A' v', LocalDecl.letBinding A' v' ∈ q.site.Γ := by
  cases e with
  | lam_esB | pi_esB | letE_esB_drop | letE_esB_inline => exact ⟨A, v, hm⟩
  | cctx_es => exact ⟨A, v, List.mem_cons_of_mem _ hm⟩
  | wk_es => exact letBinding_mem_insertAt _ _ (mem_of_list_tail hm)
  | esub_es => exact letBinding_mem_substRemove ‹_› (mem_of_list_tail hm)
  | linst_es => exact letBinding_mem_instLvlsCtx _ (mem_of_list_tail hm)
  | occ_es => exact ⟨A, v, mem_of_list_tail hm⟩
  | _ => exact ⟨A, v, mem_of_list_tail hm⟩

/-- **The blocking.** A `.letBinding` in a `wk` issuer's premise context makes
    its `wk_es` edge non-no-op: `AssumptionPrefix Γ c` (from the node's own
    `AssumpPref`) over an out-of-range cutoff covers all of `Γ`, which the let
    violates — so `ρ.length ≤ c` is impossible, `removeAt` is in-range, and no
    stale entry is born at that edge. -/
theorem wk_noOp_blocked_of_let {Eₐ : ResolvedEnv}
    {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T : Expr Nat}
    {d : LocalDecl} {c : Nat} {h : CvP E n Γ a b T}
    {E₀ : ResolvedEnv} {n₀ : Nat} {Γ₀ : LCtx}
    {S : ScopedCtx Eₐ E₀ n₀ Γ₀} {σ : Level → Level} {ρ : List Disp}
    (hq : Demand (.es (CvP.wk E n Γ a b T d c h) S σ ρ))
    {A v : Expr Nat} (hm : LocalDecl.letBinding A v ∈ Γ) :
    c < ρ.length := by
  apply Nat.lt_of_not_le
  intro hnoOp
  obtain ⟨hc, hap⟩ := wk_noOp_outOfRange hq hnoOp
  have htake : Γ.take c = Γ := List.take_of_length_le (Nat.le_of_lt hc)
  obtain ⟨_, hA'⟩ := hap _ (by rw [htake]; exact hm)
  exact LocalDecl.noConfusion hA'

/-! ## §8 the demand-side surplus witness

`routedDisp_wk_witness` localizes a surplus birth inside a `RoutedDisp`
derivation; the blocker needs it at a *demanded* `wk` issuer. The two views
coincide: `Demand.routed` builds the display lineage one row per `issued`
edge, and every `Issues` row preserves `ρ.length − Γ.length` going issuer →
child except `wk_es`, which adds `+1` exactly when it is out of range
(`removeAt` a no-op while the premise context `insertAt` is one longer).
Roots sit at canonical displays (surplus `0`), so walking a demanded query's
issue chain backward from a positive surplus must cross a no-op `wk_es`
edge — its issuer is the demanded `wk` node `wk_noOp_blocked_of_let`
needs. -/

/-- **The demand-side surplus witness.** A demanded query whose display is
    longer than its site context descends from a demanded `wk` issuer whose
    edge was a no-op (`ρ'.length ≤ c'`): every other `Issues` row preserves
    `ρ.length − Γ.length` between the issuer's and the child's site, and
    canonical displays have none. -/
theorem demand_surplus_wk {Eₐ : ResolvedEnv} {q : P2Query Eₐ}
    (hq : Demand q) : q.site.Γ.length < q.site.ρ.length →
      ∃ (E' : ResolvedEnv) (n' : Nat) (Γ' : LCtx) (a' b' T' : Expr Nat)
        (h' : CvP E' n' Γ' a' b' T') (d' : LocalDecl) (c' : Nat)
        (E₀' : ResolvedEnv) (n₀' : Nat) (Γ₀' : LCtx)
        (S' : ScopedCtx Eₐ E₀' n₀' Γ₀') (σ' : Level → Level) (ρ' : List Disp),
        ρ'.length ≤ c' ∧
          Demand (.es (CvP.wk E' n' Γ' a' b' T' d' c' h') S' σ' ρ') := by
  induction hq with
  | @rootEs E n Γ a b T h hAP S σ hσ =>
      intro hs
      have hs' : Γ.length < (S.can σ).length := hs
      rw [scopedCtx_can_length S σ] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | @rootCl E n Γ e T₁ T₂ D₁ D₂ h₁ h₂ S σ hσ =>
      intro hs
      have hs' : Γ.length < (S.can σ).length := hs
      rw [scopedCtx_can_length S σ] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | @rootEut E n Γ e T₁ T₂ D₁ D₂ h₁ h₂ S σ hσ =>
      intro hs
      have hs' : Γ.length < (S.can σ).length := hs
      rw [scopedCtx_can_length S σ] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | @rootCts E n Γ X Y w s h DX hAP hDX S =>
      intro hs
      have hs' : Γ.length < (S.can id).length := hs
      rw [scopedCtx_can_length S id] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | @rootPb E n Γ e T s D DT hD hDT S σ hσ =>
      intro hs
      have hs' : Γ.length < (S.can σ).length := hs
      rw [scopedCtx_can_length S σ] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | @rootBitCoh E n Γ T u v D₁ D₂ h₁ h₂ S σ hσ =>
      intro hs
      have hs' : Γ.length < (S.can σ).length := hs
      rw [scopedCtx_can_length S σ] at hs'
      exact absurd hs' (Nat.lt_irrefl _)
  | issued i q hdi e ih =>
      intro hs
      cases e with
      | @wk_es E n Γ a b T d c h E₀ n₀ Γ₀ S σ ρ =>
          by_cases hnoOp : ρ.length ≤ c
          · exact ⟨E, n, Γ, a, b, T, h, d, c, E₀, n₀, Γ₀, S, σ, ρ, hnoOp, hdi⟩
          · apply ih
            show (insertAt d c Γ).length < ρ.length
            have hs' : Γ.length < (removeAt ρ c).length := hs
            rw [removeAt_length_of_lt ρ (Nat.lt_of_not_ge hnoOp)] at hs'
            rw [insertAt_length]
            omega
      | @esub_es E n Γ a b T t v j u h hget hv hvT E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show (substRemove v j Γ).length < ρ.length
          have hs' : Γ.length < (insertDisp (binderDisp (levelIsZero (σ u))) j ρ).length := hs
          rw [insertDisp_length] at hs'
          have hj := getElem?_lt_length hget
          rw [substRemove_length_lt hj]
          omega
      | @lam_esB E n Γ A A' b b' B u hA hb dl dr E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show Γ.length < ρ.length
          have hs' : (.assumption A :: Γ).length
              < (binderDisp (levelIsZero (σ u)) :: ρ).length := hs
          simp only [List.length_cons] at hs'
          omega
      | @pi_esB E n Γ A A' B B' u v hA hB dl dr E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show Γ.length < ρ.length
          have hs' : (.assumption A :: Γ).length
              < (binderDisp (levelIsZero (σ u)) :: ρ).length := hs
          simp only [List.length_cons] at hs'
          omega
      | @letE_esB_drop E n Γ A A' v v' b b' B u hA hv hb dl dr E₀ n₀ Γ₀ S σ ρ hvs =>
          apply ih
          show Γ.length < ρ.length
          have hs' : (.letBinding A v :: Γ).length < (.drop :: ρ).length := hs
          simp only [List.length_cons] at hs'
          omega
      | @letE_esB_inline E n Γ A A' v v' b b' B u hA hv hb dl dr E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show Γ.length < ρ.length
          have hs' : (.letBinding A v :: Γ).length
              < (.inline (hv.dl.eps σ ρ) :: ρ).length := hs
          simp only [List.length_cons] at hs'
          omega
      | @linst_es E a' n Γ a b T ls hls hlen h E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show (instLvlsCtx ls Γ).length < ρ.length
          have hs' : Γ.length < ρ.length := hs
          unfold instLvlsCtx
          simpa only [List.length_map]
      | @cctx_es E n Γ a b T A A' u h hA E₀ n₀ Γ₀ S σ ρ =>
          apply ih
          show Γ.length + 1 < ρ.length
          have hs' : (.assumption A' :: Γ).length < ρ.length := hs
          simp only [List.length_cons] at hs'
          omega
      | @pb_letValue E n Γ e T s D DT Γ₀ S σ ρ k i hframe Γ' A₀ u₀ v₀ hΓ' hA hv
          hsel hapA hapv =>
          exfalso
          have hs' : Γ'.length < ((S.tail hΓ').can σ).length := hs
          rw [scopedCtx_can_length (S.tail hΓ') σ] at hs'
          exact absurd hs' (Nat.lt_irrefl _)
      | delta_obs_out _ _ => exact absurd hs (Nat.not_lt_zero _)
      | delta_obs_gate _ _ => exact absurd hs (Nat.not_lt_zero _)
      | _ => exact ih hs

end Rcic.Syn

#print axioms Rcic.Syn.removeAt_length_ge
#print axioms Rcic.Syn.removeAt_length_le
#print axioms Rcic.Syn.routedDisp_length_ge
#print axioms Rcic.Syn.wk_noOp_outOfRange
#print axioms Rcic.Syn.scopedCtx_can_length
#print axioms Rcic.Syn.wk_canonicalDisp_notKeep
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt_canonical
#print axioms Rcic.Syn.resolve_keep_slot
#print axioms Rcic.Syn.countKeep_take_mono_keep
#print axioms Rcic.Syn.inst_star_eq_of_closedAt
#print axioms Rcic.Syn.wkInnerGo_eq_removeAt_of_closedAt
#print axioms Rcic.Syn.wkInnerDisp_eq_removeAt_of_closedAt
#print axioms Rcic.Syn.removeAt_eq_of_ge
#print axioms Rcic.Syn.removeAt_length_of_lt
#print axioms Rcic.Syn.routedDisp_wk_witness
#print axioms Rcic.Syn.mem_of_list_tail
#print axioms Rcic.Syn.letBinding_mem_insertAt
#print axioms Rcic.Syn.letBinding_mem_substRemove
#print axioms Rcic.Syn.letBinding_mem_instLvlsCtx
#print axioms Rcic.Syn.issues_letTail
#print axioms Rcic.Syn.wk_noOp_blocked_of_let
