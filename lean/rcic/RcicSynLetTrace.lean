import rcic.RcicSynLetRel
import rcic.RcicSynWalkLet
import rcic.RcicSynBelowBoundary
import rcic.RcicSynBvarWk
import rcic.RcicSynBvarEsub
import rcic.RcicSynYes
import rcic.RcicSynInstEnd

/-!
# Wall 2 (changed-declaration letRight), step 2a — the strengthened trace

`research/rcic/sortrow/BELOWC_SEMANTIC_WALLS.md` Part III, "Strengthened trace".

The let-slot walk `bwalkAtL` (`RcicSynWalkLet`) renames one original variable through a
transport stack and returns a `BHit` — survivor (`keep`), replacement (`repl`) or
survivor-with-bridge-chain (`retype`). `BHit` discards the original side: which stack
actions acted on the variable's erasure, and which original substitution site a
replacement came from. The trace restores exactly that, as an invariant stated on
`bwalkAtL`'s own output:

* `Sites ss` mirrors the stack and records, at every `esub`/`lsub` step, the original
  site's gate `(σ, u)` (the replacement formation's sort under its stage map).
  `walkSite` follows the walk's index arithmetic and returns the hit site, if any.
* `BHitRel L site w`: a survivor at final index `j` has `Rel L (resolve ρ' j)`; a
  replacement `hv` has `Rel L (hv.eps μ' ρ')` with its ★-status fixed by the site's gate;
  `L` is the left term `applyActs acts (resolve δ i)` (the pending erased actions of the
  stack applied to the original variable's display entry).
* `TraceInv`: `BHitRel` for every index of the original local context, proved for the
  empty stack from the top display relation (`traceInv_nil`) and extended one step at a
  time (`traceInv_wk`, `traceInv_esub_keep/drop`, `traceInv_lsub_drop/inline`,
  `traceInv_linst`, `traceInv_cctx`). Each step lemma takes exactly the structural facts
  the spec names: weak `DisplayFits`, the original `AssumptionPrefix`, the site's PB
  (`r = ★ ↔ gate`), the replacement relation, and (lsub) the same-stage scope certificate
  consumed through `localize_lift_cancel` — never an ES/CL/observation answer.

The binder shift (`shiftAll`) is step 2b (`RcicSynLetTraceShift`). `closure_claim` stays 0.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 structural prefix facts -/

/-- An assumption position of a fitting display is `keep` or `drop`. -/
theorem fits_assumption_slot {Γ : LCtx} {δ : List Disp} (h : DisplayFits Γ δ) :
    ∀ (m : Nat) (A : Expr Nat), Γ.get? m = some (.assumption A) →
      δ[m]? = some .keep ∨ δ[m]? = some .drop := by
  induction h with
  | nil ρ => intro m A hm; cases m <;> simp at hm
  | assumptionKeep _ ih =>
      intro m A hm
      cases m with
      | zero => exact Or.inl (by simp)
      | succ m => simpa using ih m A (by simpa using hm)
  | assumptionDrop _ ih =>
      intro m A hm
      cases m with
      | zero => exact Or.inr (by simp)
      | succ m => simpa using ih m A (by simpa using hm)
  | letDrop _ ih =>
      intro m A hm
      cases m with
      | zero => simp at hm
      | succ m => simpa using ih m A (by simpa using hm)
  | letInline _ ih =>
      intro m A hm
      cases m with
      | zero => simp at hm
      | succ m => simpa using ih m A (by simpa using hm)

/-- Positions `≤ i` of `δ` are assumption slots. -/
def AssumpDisp (δ : List Disp) (i : Nat) : Prop :=
  ∀ m, m ≤ i → δ[m]? = some .keep ∨ δ[m]? = some .drop

/-- Under assumption slots up to `i`, `resolve δ i` is ★ or an erased slot below the
    prefix's keep count. -/
theorem resolve_assump : (δ : List Disp) → (i : Nat) → AssumpDisp δ i →
    resolve δ i = .star ∨ ∃ m, m < countKeep (δ.take (i + 1)) ∧ resolve δ i = .bvar m
  | [], i, h => by
      have := h 0 (Nat.zero_le i)
      simp at this
  | d :: δ, 0, h => by
      rcases h 0 (Nat.le_refl 0) with h0 | h0
      · simp at h0; subst h0
        exact Or.inr ⟨0, by simp [countKeep], rfl⟩
      · simp at h0; subst h0
        exact Or.inl rfl
  | d :: δ, i + 1, h => by
      have htail : AssumpDisp δ i := fun m hm => by
        have := h (m + 1) (Nat.succ_le_succ hm)
        simpa using this
      rcases h 0 (Nat.zero_le _) with h0 | h0
      · simp at h0; subst h0
        rcases resolve_assump δ i htail with hs | ⟨m, hm, hr⟩
        · exact Or.inl (by rw [resolve_keep_succ, hs]; rfl)
        · refine Or.inr ⟨m + 1, ?_, ?_⟩
          · simp only [List.take_succ_cons, countKeep]; omega
          · rw [resolve_keep_succ, hr]; simp [ETm.lift]
      · simp at h0; subst h0
        rcases resolve_assump δ i htail with hs | ⟨m, hm, hr⟩
        · exact Or.inl (by rw [resolve_drop_succ, hs])
        · exact Or.inr ⟨m, by simpa [List.take_succ_cons, countKeep] using hm,
            by rw [resolve_drop_succ, hr]⟩

theorem countKeep_take_mono (δ : List Disp) (a b : Nat) (hab : a ≤ b) :
    countKeep (δ.take a) ≤ countKeep (δ.take b) := by
  induction δ generalizing a b with
  | nil => simp
  | cons d δ ih =>
      cases a with
      | zero => simp [countKeep]
      | succ a =>
          cases b with
          | zero => omega
          | succ b =>
              have := ih a b (Nat.le_of_succ_le_succ hab)
              cases d <;> simp only [List.take_succ_cons, countKeep] <;> omega

/-- A lift at or above the prefix's keep count fixes an assumption-prefix entry. -/
theorem lift_resolve_assump {δ : List Disp} {i κ : Nat} (h : AssumpDisp δ i)
    (hκ : countKeep (δ.take (i + 1)) ≤ κ) : (resolve δ i).lift κ 1 = resolve δ i := by
  rcases resolve_assump δ i h with hs | ⟨m, hm, hr⟩
  · rw [hs]; rfl
  · rw [hr]; simp only [ETm.lift]; rw [if_neg (by omega)]

/-- An instantiation at or above the prefix's keep count fixes an assumption-prefix entry. -/
theorem inst_resolve_assump {δ : List Disp} {i κ : Nat} (r : ETm) (h : AssumpDisp δ i)
    (hκ : countKeep (δ.take (i + 1)) ≤ κ) : ETm.inst κ r (resolve δ i) = resolve δ i := by
  rcases resolve_assump δ i h with hs | ⟨m, hm, hr⟩
  · rw [hs]; rfl
  · rw [hr]; simp only [ETm.inst]; rw [if_neg (by omega), if_neg (by omega)]

theorem mem_take_of_get? : (Γ : LCtx) → (c m : Nat) → (x : LocalDecl) → m < c →
    Γ.get? m = some x → x ∈ Γ.take c
  | [], _, m, _, _, h => by cases m <;> simp at h
  | _ :: Γ, 0, _, _, hmc, _ => absurd hmc (Nat.not_lt_zero _)
  | y :: Γ, c + 1, 0, x, _, h => by
      simp at h; subst h; simp
  | y :: Γ, c + 1, m + 1, x, hmc, h => by
      simp only [List.get?_cons_succ] at h
      simp only [List.take_succ_cons, List.mem_cons]
      exact Or.inr (mem_take_of_get? Γ c m x (Nat.lt_of_succ_lt_succ hmc) h)

theorem insertAt_length_succ (d : LocalDecl) : (c : Nat) → (Γ : LCtx) →
    (insertAt d c Γ).length = Γ.length + 1
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | c + 1, _ :: Γ => by
      simp only [insertAt_succ_cons, List.length_cons]
      rw [insertAt_length_succ d c Γ]

theorem substRemove_length_succ (v : Expr Nat) : (j : Nat) → (Γ : LCtx) → j < Γ.length →
    (substRemove v j Γ).length + 1 = Γ.length
  | _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, _ :: Γ, _ => rfl
  | j + 1, _ :: Γ, h => by
      simp only [substRemove, List.length_cons]
      rw [substRemove_length_succ v j Γ (Nat.lt_of_succ_lt_succ h)]

/-- Below the cutoff, `substRemove` instantiates the entry in place. -/
theorem substRemove_get?_lt (v : Expr Nat) : {j m : Nat} → {Γ : LCtx} → {x : LocalDecl} →
    m < j → Γ.get? m = some x →
    (substRemove v j Γ).get? m = some (instDecl (j - m - 1) v x)
  | 0, m, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | j + 1, 0, [], _, _, hg => by simp at hg
  | j + 1, 0, y :: Γ, x, _, hg => by
      simp at hg; subst hg
      simp [substRemove]
  | j + 1, m + 1, [], _, _, hg => by simp at hg
  | j + 1, m + 1, y :: Γ, x, h, hg => by
      simp only [List.get?_cons_succ] at hg
      simp only [substRemove, List.get?_cons_succ]
      have ih := substRemove_get?_lt v (Nat.lt_of_succ_lt_succ h) hg
      have : j + 1 - (m + 1) - 1 = j - m - 1 := by omega
      rw [this]
      exact ih

/-- The display of a weakened context is assumption-shaped below the cutoff. -/
theorem assumpDisp_wk {Γ : LCtx} {δ : List Disp} (d : LocalDecl) {c : Nat}
    (hfit : DisplayFits (insertAt d c Γ) δ) (hAP : AssumptionPrefix Γ c) {i : Nat}
    (hi : i < c) (hlen : i < Γ.length) : AssumpDisp δ i := by
  intro m hm
  have hmΓ : m < Γ.length := Nat.lt_of_le_of_lt hm hlen
  obtain ⟨x, hx⟩ : ∃ x, Γ.get? m = some x := by
    cases hx : Γ.get? m with
    | none => exact absurd (List.get?_eq_none.mp hx) (Nat.not_le.mpr hmΓ)
    | some x => exact ⟨x, rfl⟩
  obtain ⟨A, hA⟩ := hAP x (mem_take_of_get? Γ c m x (Nat.lt_of_le_of_lt hm hi) hx)
  subst hA
  have hget := insertAt_get?_lt d (Nat.lt_of_le_of_lt hm hi) hx
  exact fits_assumption_slot hfit m _ hget

/-- The display of a substituted context is assumption-shaped below the hole. -/
theorem assumpDisp_esub {Γ : LCtx} {δ : List Disp} (v : Expr Nat) {j : Nat}
    (hfit : DisplayFits (substRemove v j Γ) δ) (hAP : AssumptionPrefix Γ j) {i : Nat}
    (hi : i < j) (hlen : i < Γ.length) : AssumpDisp δ i := by
  intro m hm
  have hmΓ : m < Γ.length := Nat.lt_of_le_of_lt hm hlen
  obtain ⟨x, hx⟩ : ∃ x, Γ.get? m = some x := by
    cases hx : Γ.get? m with
    | none => exact absurd (List.get?_eq_none.mp hx) (Nat.not_le.mpr hmΓ)
    | some x => exact ⟨x, rfl⟩
  obtain ⟨A, hA⟩ := hAP x (mem_take_of_get? Γ j m x (Nat.lt_of_le_of_lt hm hi) hx)
  subst hA
  have hget := substRemove_get?_lt v (Nat.lt_of_le_of_lt hm hi) hx
  exact fits_assumption_slot hfit m _ hget

/-! ## §2 fit preservation through the stack -/

theorem displayFits_removeAt (d : LocalDecl) : (c : Nat) → {Γ : LCtx} → {δ : List Disp} →
    DisplayFits (insertAt d c Γ) δ → DisplayFits Γ (removeAt δ c)
  | 0, Γ, δ, h => by
      rw [insertAt_zero] at h
      cases h with
      | assumptionKeep h' => exact h'
      | assumptionDrop h' => exact h'
      | letDrop h' => exact h'
      | letInline h' => exact h'
  | c + 1, [], δ, h => by
      cases δ with
      | nil => exact .nil []
      | cons x δ => exact .nil _
  | c + 1, y :: Γ, δ, h => by
      rw [insertAt_succ_cons] at h
      cases y with
      | assumption A =>
          simp only [liftDecl] at h
          cases h with
          | assumptionKeep h' =>
              simp only [removeAt]
              exact .assumptionKeep (displayFits_removeAt d c h')
          | assumptionDrop h' =>
              simp only [removeAt]
              exact .assumptionDrop (displayFits_removeAt d c h')
      | letBinding A v =>
          simp only [liftDecl] at h
          cases h with
          | letDrop h' =>
              simp only [removeAt]
              exact .letDrop (displayFits_removeAt d c h')
          | letInline h' =>
              simp only [removeAt]
              exact .letInline (displayFits_removeAt d c h')

theorem displayFits_insertDisp_assump (v : Expr Nat) : (j : Nat) → {Γ : LCtx} → {δ : List Disp} →
    {t : Expr Nat} → Γ.get? j = some (.assumption t) →
    DisplayFits (substRemove v j Γ) δ → (dd : Disp) → (dd = .keep ∨ dd = .drop) →
    DisplayFits Γ (insertDisp dd j δ)
  | _, [], _, _, hget, _, _, _ => by simp at hget
  | 0, x :: Γ, δ, t, hget, h, dd, hdd => by
      simp at hget; subst hget
      rw [substRemove_zero_cons] at h
      rw [insertDisp_zero]
      rcases hdd with hdd | hdd <;> subst hdd
      · exact .assumptionKeep h
      · exact .assumptionDrop h
  | j + 1, x :: Γ, δ, t, hget, h, dd, hdd => by
      simp only [List.get?_cons_succ] at hget
      simp only [substRemove] at h
      cases x with
      | assumption A =>
          simp only [instDecl] at h
          cases h with
          | assumptionKeep h' =>
              simp only [insertDisp]
              exact .assumptionKeep (displayFits_insertDisp_assump v j hget h' dd hdd)
          | assumptionDrop h' =>
              simp only [insertDisp]
              exact .assumptionDrop (displayFits_insertDisp_assump v j hget h' dd hdd)
      | letBinding A w =>
          simp only [instDecl] at h
          cases h with
          | letDrop h' =>
              simp only [insertDisp]
              exact .letDrop (displayFits_insertDisp_assump v j hget h' dd hdd)
          | letInline h' =>
              simp only [insertDisp]
              exact .letInline (displayFits_insertDisp_assump v j hget h' dd hdd)

theorem displayFits_insertDisp_let (v : Expr Nat) : (j : Nat) → {Γ : LCtx} → {δ : List Disp} →
    {t : Expr Nat} → Γ.get? j = some (.letBinding t v) →
    DisplayFits (substRemove v j Γ) δ → (dd : Disp) → (dd = .drop ∨ ∃ w, dd = .inline w) →
    DisplayFits Γ (insertDisp dd j δ)
  | _, [], _, _, hget, _, _, _ => by simp at hget
  | 0, x :: Γ, δ, t, hget, h, dd, hdd => by
      simp at hget; subst hget
      rw [substRemove_zero_cons] at h
      rw [insertDisp_zero]
      rcases hdd with hdd | ⟨w, hdd⟩ <;> subst hdd
      · exact .letDrop h
      · exact .letInline h
  | j + 1, x :: Γ, δ, t, hget, h, dd, hdd => by
      simp only [List.get?_cons_succ] at hget
      simp only [substRemove] at h
      cases x with
      | assumption A =>
          simp only [instDecl] at h
          cases h with
          | assumptionKeep h' =>
              simp only [insertDisp]
              exact .assumptionKeep (displayFits_insertDisp_let v j hget h' dd hdd)
          | assumptionDrop h' =>
              simp only [insertDisp]
              exact .assumptionDrop (displayFits_insertDisp_let v j hget h' dd hdd)
      | letBinding A w =>
          simp only [instDecl] at h
          cases h with
          | letDrop h' =>
              simp only [insertDisp]
              exact .letDrop (displayFits_insertDisp_let v j hget h' dd hdd)
          | letInline h' =>
              simp only [insertDisp]
              exact .letInline (displayFits_insertDisp_let v j hget h' dd hdd)

theorem displayFits_instLvlsCtx (ls : List Level) : {Γ : LCtx} → {δ : List Disp} →
    DisplayFits Γ δ → DisplayFits (instLvlsCtx ls Γ) δ
  | _, _, .nil ρ => .nil ρ
  | _, _, .assumptionKeep h => .assumptionKeep (displayFits_instLvlsCtx ls h)
  | _, _, .assumptionDrop h => .assumptionDrop (displayFits_instLvlsCtx ls h)
  | _, _, .letDrop h => .letDrop (displayFits_instLvlsCtx ls h)
  | _, _, .letInline h => .letInline (displayFits_instLvlsCtx ls h)

theorem displayFits_setAssump (A : Expr Nat) : (p : Nat) → {Γ : LCtx} → {δ : List Disp} →
    DisplayFits Γ δ → (∃ A0, Γ.get? p = some (.assumption A0)) → DisplayFits (setAssump p A Γ) δ
  | _, [], _, h, _ => by rw [setAssump_nil]; exact h
  | 0, x :: Γ, _, h, hp => by
      obtain ⟨A0, hA0⟩ := hp
      simp at hA0
      subst hA0
      rw [setAssump_zero]
      cases h with
      | assumptionKeep h' => exact .assumptionKeep h'
      | assumptionDrop h' => exact .assumptionDrop h'
  | p + 1, x :: Γ, _, h, hp => by
      obtain ⟨A0, hA0⟩ := hp
      simp only [List.get?_cons_succ] at hA0
      rw [setAssump_succ]
      cases h with
      | assumptionKeep h' => exact .assumptionKeep (displayFits_setAssump A p h' ⟨A0, hA0⟩)
      | assumptionDrop h' => exact .assumptionDrop (displayFits_setAssump A p h' ⟨A0, hA0⟩)
      | letDrop h' => exact .letDrop (displayFits_setAssump A p h' ⟨A0, hA0⟩)
      | letInline h' => exact .letInline (displayFits_setAssump A p h' ⟨A0, hA0⟩)

theorem getElem?_some_of_lt {δ : List Disp} {c : Nat} (h : c < δ.length) :
    ∃ d, δ[c]? = some d := ⟨δ[c], List.getElem?_eq_getElem h⟩

/-! ## §3 sites: the original side of the stack -/

/-- The original site data of a transport stack: at every `esub`/`lsub` step the
    replacement formation's gate `(σ, u)` — its sort `u` and the stage map `σ`. -/
inductive Sites {E : ResolvedEnv} {n : Nat} : List (PStep E n) → Type where
  | nil : Sites []
  | wk {ss : List (PStep E n)} (c : Nat) (d : LocalDecl) (s : Sites ss) : Sites (.wk c d :: ss)
  | esub {ss : List (PStep E n)} (j : Nat) (v t : Expr Nat) (Γe Γr : LCtx)
      (hget : Γe.get? j = some (.assumption t)) (repl replT : Expr Nat)
      (hv : TyP E n Γr repl replT) (σ : Level → Level) (u : Level) (s : Sites ss) :
      Sites (.esub j v t Γe Γr hget repl replT hv :: ss)
  | lsub {ss : List (PStep E n)} (j : Nat) (v t : Expr Nat) (Γe Γr : LCtx)
      (hget : Γe.get? j = some (.letBinding t v)) (repl replT : Expr Nat)
      (hv : TyP E n Γr repl replT) (σ : Level → Level) (u : Level) (s : Sites ss) :
      Sites (.lsub j v t Γe Γr hget repl replT hv :: ss)
  | linst {ss : List (PStep E n)} (ls : List Level) (a nStep : Nat)
      (hls : levelsBounded nStep ls = true) (hlen : ls.length = a) (s : Sites ss) :
      Sites (.linst ls a nStep hls hlen :: ss)
  | cctx {ss : List (PStep E n)} (p : Nat) (Askel newTy oldTy : Expr Nat) (u : Level) (Γr : LCtx)
      (hc : CvP E n Γr newTy oldTy (.sort u)) (s : Sites ss) :
      Sites (.cctx p Askel newTy oldTy u Γr hc :: ss)

/-- The hit site of an index through the stack, following `bwalkAtL`'s index arithmetic. -/
def walkSite {E : ResolvedEnv} {n : Nat} : {ss : List (PStep E n)} → Sites ss → Nat →
    Option ((Level → Level) × Level)
  | _, .nil, _ => none
  | _, .wk c _ s, i => if i < c then walkSite s i else walkSite s (i + 1)
  | _, .esub j _ _ _ _ _ _ _ _ σ u s, i =>
      if i < j then walkSite s i else if j < i then walkSite s (i - 1) else some (σ, u)
  | _, .lsub j _ _ _ _ _ _ _ _ σ u s, i =>
      if i < j then walkSite s i else if j < i then walkSite s (i - 1) else some (σ, u)
  | _, .linst _ _ _ _ _ s, i => walkSite s i
  | _, .cctx p _ _ _ _ _ _ s, i => if i = p then walkSite s p else walkSite s i

/-- The levels of a bridge chain, innermost link first. -/
def convChainLevels {E : ResolvedEnv} {n : Nat} {Γ : LCtx} : {a c : Expr Nat} →
    ConvChain E n Γ a c → List Level
  | _, _, .nil => []
  | _, _, .cons u _ rest => u :: convChainLevels rest

theorem convChainLevels_snoc {E : ResolvedEnv} {n : Nat} {Γ : LCtx} : {a b c : Expr Nat} →
    (hc : ConvChain E n Γ a b) → (u : Level) → (h : CvP E n Γ b c (.sort u)) →
    convChainLevels (hc.snoc u h) = convChainLevels hc ++ [u]
  | _, _, _, .nil, _, _ => rfl
  | _, _, _, .cons u1 h1 rest, u, h => by
      simp only [ConvChain.snoc, convChainLevels, convChainLevels_snoc rest u h, List.cons_append]

/-! ## §4 the trace invariant on `bwalkAtL`'s output -/

/-- The left term `L` against one walk result: a survivor at final index `j` is related to
    the final display's entry; a replacement is related to the stored typing's erasure,
    whose ★-status is the hit site's gate. -/
def BHitRel (tbl : List CRule) (μ' : Level → Level) (ρ' : List Disp) (L : ETm)
    (site : Option ((Level → Level) × Level)) {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty : Expr Nat} : BHit E n pre fin term ty → Prop
  | .keep j _ _ => site = none ∧ Rel tbl L (resolve ρ' j)
  | .repl hv => ∃ σo uo, site = some (σo, uo) ∧
      (hv.eps μ' ρ' = .star ↔ levelIsZero (σo uo) = true) ∧ Rel tbl L (hv.eps μ' ρ')
  | .retype j _ _ _ _ => site = none ∧ Rel tbl L (resolve ρ' j)

theorem bHitRel_castTerm {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp} {L : ETm}
    {site : Option ((Level → Level) × Level)} {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty term' : Expr Nat} (h : term' = term) (w : BHit E n pre fin term ty)
    (hw : BHitRel tbl μ' ρ' L site w) : BHitRel tbl μ' ρ' L site (BHit.castTerm h w) := by
  cases w with
  | keep j ht hl => exact hw
  | repl hv =>
      obtain ⟨σo, uo, hs, hst, hr⟩ := hw
      refine ⟨σo, uo, hs, ?_, ?_⟩
      · simpa only [eps_tyCast] using hst
      · simpa only [eps_tyCast] using hr
  | retype j B ht hl hc => exact hw

theorem bHitRel_of_eq {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp} {L L' : ETm}
    {site : Option ((Level → Level) × Level)} {E : ResolvedEnv} {n : Nat} {pre fin : LCtx}
    {term ty : Expr Nat} (hL : L' = L) {w : BHit E n pre fin term ty}
    (hw : BHitRel tbl μ' ρ' L site w) : BHitRel tbl μ' ρ' L' site w := hL ▸ hw

/-- The trace invariant: `BHitRel` for every index of the local context, with the left
    term `applyActs acts (resolve δ i)`. -/
def TraceInv (tbl : List CRule) (μ' : Level → Level) (ρ' : List Disp) {E : ResolvedEnv} {n : Nat}
    (k : Nat) (Dom' Val' : Expr Nat) (ss : List (PStep E n)) (Γ : LCtx) (δ : List Disp)
    (acts : List EAct) (hinv : EsInv ss) (hrun : RunL k Dom' Val' ss Γ) (s : Sites ss) : Prop :=
  ∀ (i : Nat) (A : Expr Nat) (hlu : lookupType Γ i = some A),
    BHitRel tbl μ' ρ' (applyActs acts (resolve δ i)) (walkSite s i)
      (bwalkAtL k Dom' Val' ss i A Γ hlu hinv hrun)

/-- The empty stack: the top display relation. -/
theorem traceInv_nil {tbl : List CRule} (hcl : TableClosed tbl) {μ' : Level → Level}
    {ρ' : List Disp} {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {Γ : LCtx}
    {δ : List Disp} (h : DispRel tbl δ ρ') :
    TraceInv tbl μ' ρ' k Dom' Val' ([] : List (PStep E n)) Γ δ [] .nil .nil .nil := by
  intro i A hlu
  unfold bwalkAtL walkSite
  exact ⟨rfl, rel_resolve hcl h i⟩

/-! ## §5 one step at a time -/

/-- The pending actions after a `wk` at cutoff `c`: a kept slot lifts, anything else is
    erased-silent. -/
def wkActs (δ : List Disp) (c : Nat) (acts : List EAct) : List EAct :=
  match δ[c]? with
  | some .keep => .lift (countKeep (δ.take c)) :: acts
  | _ => acts

theorem wkActs_keep {δ : List Disp} {c : Nat} (h : δ[c]? = some .keep) (acts : List EAct) :
    wkActs δ c acts = .lift (countKeep (δ.take c)) :: acts := by
  simp only [wkActs, h]

theorem wkActs_drop {δ : List Disp} {c : Nat} (h : δ[c]? = some .drop) (acts : List EAct) :
    wkActs δ c acts = acts := by
  simp only [wkActs, h]

theorem wkActs_inline {δ : List Disp} {c : Nat} {v : ETm} (h : δ[c]? = some (.inline v))
    (acts : List EAct) : wkActs δ c acts = acts := by
  simp only [wkActs, h]

theorem eActsNonStar_wkActs (δ : List Disp) (c : Nat) {acts : List EAct}
    (h : EActsNonStar acts) : EActsNonStar (wkActs δ c acts) := by
  unfold wkActs
  split
  · exact h
  · exact h

/-- Step `wk c d`: survivors below the cutoff keep their index and their erasure (the
    assumption prefix is fixed by the lift), survivors at or above shift by one. -/
theorem traceInv_wk {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp} {E : ResolvedEnv}
    {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)} {Γ : LCtx}
    {δ : List Disp} {acts : List EAct} {hinv : EsInv ss} (c : Nat) (d : LocalDecl)
    {hrun : RunL k Dom' Val' ss (insertAt d c Γ)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (insertAt d c Γ) δ acts hinv hrun s)
    (hfit : DisplayFits (insertAt d c Γ) δ) (hAP : AssumptionPrefix Γ c) :
    TraceInv tbl μ' ρ' k Dom' Val' (.wk c d :: ss) Γ (removeAt δ c) (wkActs δ c acts)
      (.wk c d hinv) (.wk c d hrun) (.wk c d s) := by
  intro i A hlu
  have hiΓ : i < Γ.length := lt_length_of_lookupType_some hlu
  have hlenδ : Γ.length + 1 ≤ δ.length := by
    have := hfit.length_le
    rw [insertAt_length_succ] at this
    exact this
  unfold bwalkAtL
  split
  · rename_i hi
    simp only [walkSite, if_pos hi]
    refine bHitRel_castTerm _ _ (bHitRel_of_eq ?_ (h i (lift c 1 A) (lookupType_insertAt_lt d hi hlu)))
    rw [resolve_removeAt_lo δ c i hi]
    have hAD : AssumpDisp δ i := assumpDisp_wk d hfit hAP hi hiΓ
    have hκ : countKeep (δ.take (i + 1)) ≤ countKeep (δ.take c) :=
      countKeep_take_mono δ (i + 1) c hi
    unfold wkActs
    split
    · rename_i hk
      rw [applyActs_cons]
      show applyActs acts ((resolve δ i).lift (countKeep (δ.take c)) 1) = _
      rw [lift_resolve_assump hAD hκ]
    · rfl
  · rename_i hi
    have hci : c ≤ i := Nat.le_of_not_lt hi
    simp only [walkSite, if_neg hi]
    refine bHitRel_castTerm _ _
      (bHitRel_of_eq ?_ (h (i + 1) (lift c 1 A) (lookupType_insertAt_ge d hci hlu)))
    have hcδ : c < δ.length := by omega
    obtain ⟨dc, hdc⟩ := getElem?_some_of_lt hcδ
    cases dc with
    | keep =>
        rw [wkActs_keep hdc, applyActs_cons]
        show applyActs acts ((resolve (removeAt δ c) i).lift (countKeep (δ.take c)) 1) = _
        rw [resolve_removeAt_hi_keep δ c i hci hdc]
    | drop =>
        rw [wkActs_drop hdc, resolve_removeAt_hi_drop δ c i hci hdc]
    | inline v =>
        rw [wkActs_inline hdc, resolve_removeAt_hi_inline δ c i v hci hdc]

/-- Step `esub` at a retained hole (bit `false`): the left action is `inst κ r`; below the
    hole the assumption prefix is fixed, above it `inst_lift_id` cancels the inserted
    keep, and the hit returns the replacement `r` under the outer actions. -/
theorem traceInv_esub_keep {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ0 : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx} (hget : Γe.get? j = some (.assumption t))
    {repl replT : Expr Nat} (hvS : TyP E n Γr repl replT)
    (hΓ : Γ0 = Γe) (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
    (hr : repl = Skels.app (steps ss) (lift 0 j v)) (hT : replT = Skels.app (steps ss) (lift 0 j t))
    {hrun : RunL k Dom' Val' ss (substRemove v j Γ0)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (substRemove v j Γ0) δ acts hinv hrun s)
    (hfit : DisplayFits (substRemove v j Γ0) δ) (hAP : AssumptionPrefix Γ0 j)
    (hns : EActsNonStar acts)
    (σo : Level → Level) (uo : Level) (r : ETm)
    (hpb : r = .star ↔ levelIsZero (σo uo) = true) (hbit : levelIsZero (σo uo) = false)
    (hrel : Rel tbl (applyActs acts r) (hvS.eps μ' ρ')) :
    TraceInv tbl μ' ρ' k Dom' Val' (.esub j v t Γe Γr hget repl replT hvS :: ss) Γ0
      (insertDisp .keep j δ) (.inst (countKeep (δ.take j)) r :: acts)
      (.esub j v t Γe Γr hget repl replT hvS hinv hr hT) (.esub hΓ hctx hrun)
      (.esub j v t Γe Γr hget repl replT hvS σo uo s) := by
  intro i A hlu
  have hne : r ≠ .star := fun hs => by rw [hpb] at hs; rw [hs] at hbit; cases hbit
  have hjΓ : j < Γ0.length := by
    rw [hΓ]
    exact lt_length_of_get? Γe j hget
  have hjδ : j ≤ δ.length := by
    have h1 := hfit.length_le
    have h2 := substRemove_length_succ v j Γ0 hjΓ
    omega
  unfold bwalkAtL
  split
  · rename_i hi
    simp only [walkSite, if_pos hi]
    have hiΓ : i < Γ0.length := lt_length_of_lookupType_some hlu
    refine bHitRel_castTerm _ _
      (bHitRel_of_eq ?_ (h i _ (lookupType_substRemove_lt hi hlu)))
    rw [applyActs_cons]
    show applyActs acts (ETm.inst (countKeep (δ.take j)) r (resolve (insertDisp .keep j δ) i)) = _
    rw [resolve_insertDisp_lo .keep δ j i hi hjδ]
    have hAD : AssumpDisp δ i := assumpDisp_esub v hfit hAP hi hiΓ
    rw [inst_resolve_assump r hAD (countKeep_take_mono δ (i + 1) j hi)]
  · split
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_pos hj]
      refine bHitRel_castTerm _ _
        (bHitRel_of_eq ?_ (h (i - 1) _ (lookupType_substRemove_gt hj hlu)))
      rw [applyActs_cons]
      show applyActs acts (ETm.inst (countKeep (δ.take j)) r (resolve (insertDisp .keep j δ) i)) = _
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [resolve_insertDisp_hi_keep δ j i' (Nat.le_of_lt_succ hj) hjδ, ETm.inst_lift_id]
      rfl
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_neg hj]
      generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
      cases e
      refine ⟨σo, uo, rfl, ?_, ?_⟩
      · rw [eps_tyCastCtx, eps_tyCast]
        constructor
        · intro hs
          have := hrel.eq_star' hs
          rw [applyActs_eq_star_iff acts hns] at this
          exact hpb.mp this
        · intro hb
          rw [hb] at hbit
          cases hbit
      · rw [eps_tyCastCtx, eps_tyCast, applyActs_cons]
        simp only [EAct.apply]
        rw [resolve_insertDisp_keep _ δ hjδ, inst_bvar_hit]
        exact hrel

/-- Step `esub` at a dropped hole (bit `true`): no erased action; the hit is ★ on both
    sides (the site's gate is `true`, so the stored replacement erases to ★). -/
theorem traceInv_esub_drop {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ0 : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx} (hget : Γe.get? j = some (.assumption t))
    {repl replT : Expr Nat} (hvS : TyP E n Γr repl replT)
    (hΓ : Γ0 = Γe) (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
    (hr : repl = Skels.app (steps ss) (lift 0 j v)) (hT : replT = Skels.app (steps ss) (lift 0 j t))
    {hrun : RunL k Dom' Val' ss (substRemove v j Γ0)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (substRemove v j Γ0) δ acts hinv hrun s)
    (hfit : DisplayFits (substRemove v j Γ0) δ)
    (hns : EActsNonStar acts)
    (σo : Level → Level) (uo : Level) (r : ETm)
    (hpb : r = .star ↔ levelIsZero (σo uo) = true) (hbit : levelIsZero (σo uo) = true)
    (hrel : Rel tbl (applyActs acts r) (hvS.eps μ' ρ')) :
    TraceInv tbl μ' ρ' k Dom' Val' (.esub j v t Γe Γr hget repl replT hvS :: ss) Γ0
      (insertDisp .drop j δ) acts
      (.esub j v t Γe Γr hget repl replT hvS hinv hr hT) (.esub hΓ hctx hrun)
      (.esub j v t Γe Γr hget repl replT hvS σo uo s) := by
  intro i A hlu
  have hrs : r = .star := hpb.mpr hbit
  have hjΓ : j < Γ0.length := by
    rw [hΓ]
    exact lt_length_of_get? Γe j hget
  have hjδ : j ≤ δ.length := by
    have h1 := hfit.length_le
    have h2 := substRemove_length_succ v j Γ0 hjΓ
    omega
  have hstar : hvS.eps μ' ρ' = .star := by
    subst hrs
    exact hrel.eq_star (applyActs_star acts)
  unfold bwalkAtL
  split
  · rename_i hi
    simp only [walkSite, if_pos hi]
    refine bHitRel_castTerm _ _
      (bHitRel_of_eq ?_ (h i _ (lookupType_substRemove_lt hi hlu)))
    rw [resolve_insertDisp_lo .drop δ j i hi hjδ]
  · split
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_pos hj]
      refine bHitRel_castTerm _ _
        (bHitRel_of_eq ?_ (h (i - 1) _ (lookupType_substRemove_gt hj hlu)))
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [resolve_insertDisp_hi_drop δ j i' (Nat.le_of_lt_succ hj) hjδ]
      rfl
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_neg hj]
      generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
      cases e
      refine ⟨σo, uo, rfl, ?_, ?_⟩
      · rw [eps_tyCastCtx, eps_tyCast, hstar]
        exact ⟨fun _ => hbit, fun _ => rfl⟩
      · rw [eps_tyCastCtx, eps_tyCast, hstar, resolve_insertDisp_drop _ δ hjδ, applyActs_star]
        exact Rel.star tbl

/-- Step `lsub` at a ★ value: as `esub` at a dropped hole. -/
theorem traceInv_lsub_drop {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ0 : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx} (hget : Γe.get? j = some (.letBinding t v))
    {repl replT : Expr Nat} (hvS : TyP E n Γr repl replT)
    (hΓ : Γ0 = Γe) (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
    (hr : repl = Skels.app (steps ss) (lift 0 j v)) (hT : replT = Skels.app (steps ss) (lift 0 j t))
    {hrun : RunL k Dom' Val' ss (substRemove v j Γ0)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (substRemove v j Γ0) δ acts hinv hrun s)
    (hfit : DisplayFits (substRemove v j Γ0) δ)
    (σo : Level → Level) (uo : Level) (r : ETm)
    (hpb : r = .star ↔ levelIsZero (σo uo) = true) (hrs : r = .star)
    (hrel : Rel tbl (applyActs acts r) (hvS.eps μ' ρ')) :
    TraceInv tbl μ' ρ' k Dom' Val' (.lsub j v t Γe Γr hget repl replT hvS :: ss) Γ0
      (insertDisp .drop j δ) acts
      (.lsub j v t Γe Γr hget repl replT hvS hinv hr hT) (.lsub hΓ hctx hrun)
      (.lsub j v t Γe Γr hget repl replT hvS σo uo s) := by
  intro i A hlu
  have hbit : levelIsZero (σo uo) = true := hpb.mp hrs
  have hjΓ : j < Γ0.length := by
    rw [hΓ]
    exact lt_length_of_get? Γe j hget
  have hjδ : j ≤ δ.length := by
    have h1 := hfit.length_le
    have h2 := substRemove_length_succ v j Γ0 hjΓ
    omega
  have hstar : hvS.eps μ' ρ' = .star := by
    subst hrs
    exact hrel.eq_star (applyActs_star acts)
  unfold bwalkAtL
  split
  · rename_i hi
    simp only [walkSite, if_pos hi]
    refine bHitRel_castTerm _ _
      (bHitRel_of_eq ?_ (h i _ (lookupType_substRemove_lt hi hlu)))
    rw [resolve_insertDisp_lo .drop δ j i hi hjδ]
  · split
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_pos hj]
      refine bHitRel_castTerm _ _
        (bHitRel_of_eq ?_ (h (i - 1) _ (lookupType_substRemove_gt hj hlu)))
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [resolve_insertDisp_hi_drop δ j i' (Nat.le_of_lt_succ hj) hjδ]
      rfl
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_neg hj]
      generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
      cases e
      refine ⟨σo, uo, rfl, ?_, ?_⟩
      · rw [eps_tyCastCtx, eps_tyCast, hstar]
        exact ⟨fun _ => hbit, fun _ => rfl⟩
      · rw [eps_tyCastCtx, eps_tyCast, hstar, resolve_insertDisp_drop _ δ hjδ, applyActs_star]
        exact Rel.star tbl

/-- Step `lsub` at a non-★ value: the display inlines the localized value and the hit
    restores it through the same-stage scope certificate (`localize_lift_cancel`). -/
theorem traceInv_lsub_inline {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ0 : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    {j : Nat} {v t : Expr Nat} {Γe Γr : LCtx} (hget : Γe.get? j = some (.letBinding t v))
    {repl replT : Expr Nat} (hvS : TyP E n Γr repl replT)
    (hΓ : Γ0 = Γe) (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (substRemove v j Γ0)))
    (hr : repl = Skels.app (steps ss) (lift 0 j v)) (hT : replT = Skels.app (steps ss) (lift 0 j t))
    {hrun : RunL k Dom' Val' ss (substRemove v j Γ0)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (substRemove v j Γ0) δ acts hinv hrun s)
    (hfit : DisplayFits (substRemove v j Γ0) δ)
    (hns : EActsNonStar acts)
    (σo : Level → Level) (uo : Level) (r : ETm)
    (hpb : r = .star ↔ levelIsZero (σo uo) = true) (hne : r ≠ .star)
    (hscope : AvoidPrefix (countKeep (δ.take j)) 0 r)
    (hrel : Rel tbl (applyActs acts r) (hvS.eps μ' ρ')) :
    TraceInv tbl μ' ρ' k Dom' Val' (.lsub j v t Γe Γr hget repl replT hvS :: ss) Γ0
      (insertDisp (.inline (localize (countKeep (δ.take j)) r)) j δ) acts
      (.lsub j v t Γe Γr hget repl replT hvS hinv hr hT) (.lsub hΓ hctx hrun)
      (.lsub j v t Γe Γr hget repl replT hvS σo uo s) := by
  intro i A hlu
  have hjΓ : j < Γ0.length := by
    rw [hΓ]
    exact lt_length_of_get? Γe j hget
  have hjδ : j ≤ δ.length := by
    have h1 := hfit.length_le
    have h2 := substRemove_length_succ v j Γ0 hjΓ
    omega
  unfold bwalkAtL
  split
  · rename_i hi
    simp only [walkSite, if_pos hi]
    refine bHitRel_castTerm _ _
      (bHitRel_of_eq ?_ (h i _ (lookupType_substRemove_lt hi hlu)))
    rw [resolve_insertDisp_lo _ δ j i hi hjδ]
  · split
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_pos hj]
      refine bHitRel_castTerm _ _
        (bHitRel_of_eq ?_ (h (i - 1) _ (lookupType_substRemove_gt hj hlu)))
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [resolve_insertDisp_hi_inline δ j i' _ (Nat.le_of_lt_succ hj) hjδ]
      rfl
    · rename_i hi hj
      simp only [walkSite, if_neg hi, if_neg hj]
      generalize hg : Nat.le_antisymm (Nat.le_of_not_lt hj) (Nat.le_of_not_lt hi) = e
      cases e
      refine ⟨σo, uo, rfl, ?_, ?_⟩
      · rw [eps_tyCastCtx, eps_tyCast]
        constructor
        · intro hs
          have := hrel.eq_star' hs
          rw [applyActs_eq_star_iff acts hns] at this
          exact hpb.mp this
        · intro hb
          exact absurd (hpb.mpr hb) hne
      · rw [eps_tyCastCtx, eps_tyCast, resolve_insertDisp_inline _ _ δ hjδ,
          localize_lift_cancel hscope]
        exact hrel

/-- Step `linst`: the display and the actions are unchanged. -/
theorem traceInv_linst {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    (ls : List Level) (a nStep : Nat) (hls : levelsBounded nStep ls = true) (hlen : ls.length = a)
    {hrun : RunL k Dom' Val' ss (instLvlsCtx ls Γ)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (instLvlsCtx ls Γ) δ acts hinv hrun s) :
    TraceInv tbl μ' ρ' k Dom' Val' (.linst ls a nStep hls hlen :: ss) Γ δ acts
      (.linst ls a nStep hls hlen hinv) (.linst ls a nStep hls hlen hrun)
      (.linst ls a nStep hls hlen s) := by
  intro i A hlu
  unfold bwalkAtL
  simp only [walkSite]
  exact h i _ (lookupType_instLvlsCtx_some ls hlu)

/-- Step `cctx` at `p`: the display and the actions are unchanged; the variable at `p`
    acquires one more bridge link, a replacement passes through a `conv`. -/
theorem traceInv_cctx {tbl : List CRule} {μ' : Level → Level} {ρ' : List Disp}
    {E : ResolvedEnv} {n : Nat} {k : Nat} {Dom' Val' : Expr Nat} {ss : List (PStep E n)}
    {Γ : LCtx} {δ : List Disp} {acts : List EAct} {hinv : EsInv ss}
    (p : Nat) (Askel newTy oldTy : Expr Nat) (u : Level) {Γr : LCtx}
    (hc : CvP E n Γr newTy oldTy (.sort u)) (Aold : Expr Nat)
    (hdec : Γ.get? p = some (.assumption Aold))
    (hnew : newTy = Skels.app (steps ss) (lift 0 (p + 1) Askel))
    (hold : oldTy = Skels.app (steps ss) (lift 0 (p + 1) Aold))
    (hctx : Γr = setLetB k Dom' Val' (Skels.ctx (steps ss) (setAssump p Askel Γ)))
    {hrun : RunL k Dom' Val' ss (setAssump p Askel Γ)} {s : Sites ss}
    (h : TraceInv tbl μ' ρ' k Dom' Val' ss (setAssump p Askel Γ) δ acts hinv hrun s) :
    TraceInv tbl μ' ρ' k Dom' Val' (.cctx p Askel newTy oldTy u Γr hc :: ss) Γ δ acts
      (.cctx p Askel newTy oldTy u Γr hc hinv)
      (.cctx p Askel newTy oldTy u Aold hdec hnew hold hctx hrun)
      (.cctx p Askel newTy oldTy u Γr hc s) := by
  intro i A hlu
  unfold bwalkAtL
  split
  · rename_i hip
    simp only [walkSite, if_pos hip]
    subst hip
    try dsimp only
    split
    · rename_i j hterm hlook heq
      have hw := h _ _ (lookupType_setAssump_at Askel Γ _ hlu)
      rw [heq] at hw
      exact hw
    · rename_i hv' heq
      have hw := h _ _ (lookupType_setAssump_at Askel Γ _ hlu)
      rw [heq] at hw
      obtain ⟨σo, uo, hs, hst, hr⟩ := hw
      refine ⟨σo, uo, hs, ?_, ?_⟩
      · simpa only [eps_tyCast, eps_conv] using hst
      · simpa only [eps_tyCast, eps_conv] using hr
    · rename_i j B hterm hlook hc' heq
      have hw := h _ _ (lookupType_setAssump_at Askel Γ _ hlu)
      rw [heq] at hw
      exact hw
  · rename_i hip
    simp only [walkSite, if_neg hip]
    exact h i A (lookupType_setAssump_ne hip hlu)

end Rcic.Syn

#print axioms Rcic.Syn.fits_assumption_slot
#print axioms Rcic.Syn.resolve_assump
#print axioms Rcic.Syn.lift_resolve_assump
#print axioms Rcic.Syn.inst_resolve_assump
#print axioms Rcic.Syn.assumpDisp_wk
#print axioms Rcic.Syn.assumpDisp_esub
#print axioms Rcic.Syn.displayFits_removeAt
#print axioms Rcic.Syn.displayFits_insertDisp_assump
#print axioms Rcic.Syn.displayFits_insertDisp_let
#print axioms Rcic.Syn.displayFits_setAssump
#print axioms Rcic.Syn.walkSite
#print axioms Rcic.Syn.convChainLevels_snoc
#print axioms Rcic.Syn.bHitRel_castTerm
#print axioms Rcic.Syn.traceInv_nil
#print axioms Rcic.Syn.traceInv_wk
#print axioms Rcic.Syn.traceInv_esub_keep
#print axioms Rcic.Syn.traceInv_esub_drop
#print axioms Rcic.Syn.traceInv_lsub_drop
#print axioms Rcic.Syn.traceInv_lsub_inline
#print axioms Rcic.Syn.traceInv_linst
#print axioms Rcic.Syn.traceInv_cctx
