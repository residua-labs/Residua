import rcic.RcicSynRouteRequests
import rcic.RcicSynSlotOrigin
import rcic.RcicSynBelowCFix
import rcic.RcicSynBelowScoped
import rcic.RcicSynEnrich
import rcic.RcicSynSpineComb
import rcic.RcicSynPBitAll
import rcic.RcicSynAppBvarPBit
import rcic.RcicSynBvarExpose
import rcic.RcicSynPack
import rcic.RcicSynZetaMeasureRefute
import rcic.RcicSynErase
import rcic.RcicLevelZero
import rcic.RcicSynSubst
import rcic.RcicTypedLevels

/-!
# S16 §2.2–§2.6 — `SlotPlan` over `DisplayRoute`

`research/rcic/sortrow/S16_BVAR_CCTX_IOTA_STEPS.md` §2.2–§2.6 on the p-auth
`DisplayRoute` layer (`RcicSynDisplayRoute` / `RcicSynRouteRequests`).
`closure_claim = 0`: this module records plans, operation codes and pending
request codes; it never stores an answer, and `entryBit` is computed from the
resolve operation the route actually performs — never defined as `hA`'s bit.

- `SlotData`/`SlotPlan`: §2.2's read of one context slot along a route —
  original occurrence, original kind (`introduced`/`ambient`/`transported`),
  S21 §1.1's origin family (`K`/`V`/`R`/`N` by real owner), both domain and
  term `ParentRole`s, the original domain-provider reference + the map at
  the provider's own place, let value/type references + their actual route,
  the slot's current entry, the ordered pending transport-action stack
  (`PendingAction`, answer-free), the resolve operation `ρ[i]?`, and the
  gate-alignment request codes still to obtain (`SlotRequest`).
- `slotPlan_resolve_op`/`slotPlan_resolve_star`: pure route algebra —
  `resolve (eval r).disp i = .star` iff the plan's computed `entryBit`.
- `slotPlan_resolve_of_answers`: §2.5 verbatim — consumes the named
  `halign`/`hBit` answers; supplies neither.
- `bvar_bit_request_below`: §2.1's `BitCoh σ hA DT` request strictly below
  the `TyP.bvar` PBit query (main's `combLexDM_pbit_bvar_sort`).
- `slot_value_request_below` / `slot_value_request_below_of_ctx`: §2.3's
  ambient-let value PB — strict original-prefix descent, plus the equal-
  length composition through main's `combLexDM_pbit_bvar_let_zero`.
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §0 — the entry's declared type and `get?`-level moves -/

/-- The declared type carried by a context entry. -/
def LocalDecl.ty : LocalDecl → Expr Nat
  | .assumption A | .letBinding A _ => A

/-- Whether a context entry carries a let value. -/
def declIsLet : LocalDecl → Bool
  | .letBinding _ _ => true
  | .assumption _ => false

/-- A successful `lookupType` reads a real entry. -/
def get?_of_lookupType {Γ : LCtx} {i : Nat} {A : Expr Nat}
    (h : lookupType Γ i = some A) : Σ' d, Γ.get? i = some d := by
  unfold lookupType at h
  split at h
  · rename_i hget; exact ⟨_, hget⟩
  · rename_i hget; exact ⟨_, hget⟩
  · contradiction

/-- `wk` (`insertAt d c`): a source entry at `i < c` keeps index `i`
    (lifted at its own cutoff by `insertAt`'s `liftDecl c`). -/
noncomputable def exists_get?_insertAt_lt (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {e : LocalDecl} (hc : i < c) (h : Γ.get? i = some e) :
    Σ' e', (insertAt d c Γ).get? i = some e' := by
  induction Γ generalizing c i with
  | nil => simp at h
  | cons x Γ ih' =>
      cases c with
      | zero => omega
      | succ c =>
          cases i with
          | zero => exact ⟨liftDecl c x, by simp⟩
          | succ i =>
              simp only [insertAt_succ_cons, List.get?_cons_succ]
              exact ih' (Nat.lt_of_succ_lt_succ hc) h

/-- `wk` (`insertAt d c`): a source entry at `i ≥ c` moves to `i + 1`
    (lifted at its own cutoff by `insertAt`'s `liftDecl c`). -/
noncomputable def exists_get?_insertAt_ge (d : LocalDecl) {c i : Nat} {Γ : LCtx}
    {e : LocalDecl} (hc : c ≤ i) (h : Γ.get? i = some e) :
    Σ' e', (insertAt d c Γ).get? (i + 1) = some e' := by
  induction Γ generalizing c i with
  | nil => simp at h
  | cons x Γ ih' =>
      cases c with
      | zero =>
          rw [insertAt_zero, List.get?_cons_succ]
          exact ⟨e, h⟩
      | succ c =>
          cases i with
          | zero => omega
          | succ i =>
              simp only [insertAt_succ_cons, List.get?_cons_succ]
              exact ih' (Nat.succ_le_succ_iff.mp hc) h

/-- `esub`/`lsub` (`substRemove v j`): a source entry at `i < j` keeps
    index `i` (instantiated by `substRemove`'s `instDecl`). -/
noncomputable def exists_get?_substRemove_lt (v : Expr Nat) {j i : Nat} {Γ : LCtx}
    {e : LocalDecl} (hc : i < j) (h : Γ.get? i = some e) :
    Σ' e', (substRemove v j Γ).get? i = some e' := by
  induction Γ generalizing j i with
  | nil => simp at h
  | cons x Γ ih' =>
      cases j with
      | zero => omega
      | succ j =>
          cases i with
          | zero => exact ⟨instDecl j v x, by simp⟩
          | succ i =>
              simp only [substRemove_succ_cons, List.get?_cons_succ]
              exact ih' (Nat.lt_of_succ_lt_succ hc) h

/-- `esub`/`lsub` (`substRemove v j`): a source entry at `i > j` moves to
    `i - 1` (instantiated by `substRemove`'s `instDecl`). The `i = j` entry
    is consumed by the edge — it has no target index (its plan is built
    from the site, not by recursion). -/
noncomputable def exists_get?_substRemove_gt (v : Expr Nat) {j i : Nat} {Γ : LCtx}
    {e : LocalDecl} (hc : j < i) (h : Γ.get? i = some e) :
    Σ' e', (substRemove v j Γ).get? (i - 1) = some e' := by
  induction Γ generalizing j i with
  | nil => simp at h
  | cons x Γ ih' =>
      cases j with
      | zero =>
          cases i with
          | zero => omega
          | succ i =>
              have h' : Γ.get? i = some e := by
                simpa only [List.get?_cons_succ] using h
              exact ⟨e, by rw [substRemove_zero_cons]; simpa using h'⟩
      | succ j =>
          cases i with
          | zero => omega
          | succ i =>
              cases i with
              | zero => exact ⟨instDecl j v x, by simp⟩
              | succ i =>
                  simp only [substRemove_succ_cons, List.get?_cons_succ]
                  have h' : Γ.get? (i + 1) = some e := h
                  obtain ⟨e', he'⟩ := ih' (Nat.succ_lt_succ_iff.mp hc) h'
                  exact ⟨e', he'⟩

/-! ## §2.2 — `SlotOriginKind`, `SlotRequest`, `SlotData`, `SlotPlan` -/

/- §2.2's original-kind trichotomy reuses main's `SlotOriginKind`
   (`RcicSynSlotOrigin`): `ambient` for entries already in the root working
   scope, `binderIntroduced` when the last edge opened the binder,
   `ambientTransported` when a transport edge carried/consumed it. The
   receipt-carrying `SlotOrigin`/`AmbientReceipt`/`TransportedAmbient`/
   `BinderDomain` layer is main's; the plan records the kind tag only. -/

/-- S21 §1.1's origin families, distinguished by the entry's real owner —
    never by the current `Disp` tag: `K` an ambient assumption (or its
    surviving keep/drop route), `V` an ambient stored let value, `R` a real
    explicit replacement (esub/lsub site), `N` a binder introduced by a real
    pi/lam/letE node. -/
inductive OriginFamily : Type where
  | K | V | R | N
  deriving DecidableEq

/-- S21 §1.3's pending transport actions — the ordered stack `F_m ∘ … ∘ F_1`
    recorded in forward application order as the walk crosses each edge.
    Codes only: a relevant esub still needs its own target-route `PB[V,W]`,
    a localized lsub its stage's scope certificate; neither is stored here. -/
inductive PendingAction : Type where
  | wkLift (d : LocalDecl) (c : Nat)
  | esubAct (j : Nat)
  | lsubAct (j : Nat)
  | linstAct (ls : List Level)
  | ewkAct
  | cctxAct
  | tailMove (k : Nat)
  deriving DecidableEq

/-- §2.4's gate-alignment request codes and §2.3's value-PB code — original
    references and operation codes only; no answer fields. -/
inductive SlotRequest (F : RawForest) : Type where
  | prepaid (use : FieldPath F) : SlotRequest F
  | providerAlign (provider : DRef F) : SlotRequest F
  | movedMixed (provider : DRef F) : SlotRequest F
  | valuePB (value type : DRef F) : SlotRequest F

/-- The plan's original data: references, entries, maps and codes.
    `valueRoute`, when present, is the real route prefix whose end place owns
    the original value/type typings. S21 §1.1's added read: `family` is the
    real owner's origin family; `domRole`/`termRole` are the parent roles the
    domain provider and the term/value occurrence actually occupy;
    `actions` is the pending transport-action stack (answer-free codes). -/
structure SlotData (F : RawForest) : Type where
  occurrence : FieldPath F
  origin : SlotOriginKind
  family : OriginFamily
  domRole : ParentRole
  termRole : ParentRole
  provider : DRef F
  providerMap : Level → Level
  valueRef : Option (DRef F)
  typeRef : Option (DRef F)
  valueRoute : Option (PSigma fun q : Place => DisplayRoute F q)
  entry : LocalDecl
  actions : List PendingAction
  pending : List (SlotRequest F)

/-- §2.2's `SlotPlan F r i A`: the original data plus `resolveOp` — the
    disposition `resolve` performs on slot `i`, read verbatim off the
    computed route state. No `resolve ρ i = .star ↔ …` and no
    `entryBit = levelIsZero (σ u)` is stored. -/
structure SlotPlan (F : RawForest) {p : Place} (r : DisplayRoute F p)
    (i : Nat) (A : Expr Nat) extends SlotData F where
  resolveOp : Option Disp

/-- `entryBit` is computed from the plan's own operation data (`resolveOp`),
    i.e. from what the current resolve performs on the original slot — never
    defined as `hA`'s bit. -/
def SlotPlan.entryBit {F : RawForest} {p : Place} {r : DisplayRoute F p}
    {i : Nat} {A : Expr Nat} (pl : SlotPlan F r i A) : Bool :=
  match pl.resolveOp with
  | some .drop => true
  | some (.inline .star) => true
  | _ => false

/-! ## §2.2 — the structural walk -/

/-- §2.2's structural reader: walk the route's last edge, map the slot index
    back to the previous place's index (or read the site's own payload when
    the edge introduced/consumed the entry), and collect the original data.
    `resolveOp` is filled uniformly by `slotPlan`. -/
noncomputable def slotDataOf {F : RawForest} {p : Place} (r : DisplayRoute F p)
    {i : Nat} (h : Σ' d, p.ctx.get? i = some d) : SlotData F := by
  induction r generalizing i with
  | root s =>
      obtain ⟨d, _⟩ := h
      exact { occurrence := s.owner, origin := .ambient,
              family := if declIsLet d then .V else .K,
              domRole := .ascribedType,
              termRole := if declIsLet d then .storedValue else .term,
              provider := .original s.owner, providerMap := s.σ,
              valueRef := if declIsLet d then some (.original s.owner) else none,
              typeRef := if declIsLet d then some (.original s.owner) else none,
              valueRoute := none, entry := d, actions := [],
              pending := if declIsLet d
                then [.valuePB (.original s.owner) (.original s.owner)]
                else [.providerAlign (.original s.owner)] }
  | step r' e ih =>
      cases e with
      | assumeBody s =>
          obtain ⟨d, hd⟩ := h
          have hchild : s.child.ctx = .assumption s.payload.A :: s.Γ := by
            rw [s.hchild]
          rw [hchild] at hd
          cases i with
          | zero =>
              exact { occurrence := s.owner, origin := .binderIntroduced,
                      family := .N, domRole := .binderDomain, termRole := .term,
                      provider := .original ⟨s.owner.nodePath ++ [s.owner.field], 0⟩,
                      providerMap := (eval r').map,
                      valueRef := none, typeRef := none, valueRoute := none,
                      entry := .assumption s.payload.A, actions := [],
                      pending := [.prepaid s.owner] }
          | succ j =>
              have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                ⟨d, by rw [s.hparent]; exact hd⟩
              exact (ih hsrc)
      | letBody s =>
          obtain ⟨d, hd⟩ := h
          have hchild : s.child.ctx = .letBinding s.A s.value :: s.Γ := by
            rw [s.hchild]
          rw [hchild] at hd
          cases i with
          | zero =>
              exact { occurrence := s.owner, origin := .binderIntroduced,
                      family := .N, domRole := .binderDomain,
                      termRole := .storedValue,
                      provider := .original ⟨s.owner.nodePath ++ [s.owner.field], 0⟩,
                      providerMap := (eval r').map,
                      valueRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                      typeRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 0⟩),
                      valueRoute := some ⟨s.parent, r'⟩,
                      entry := .letBinding s.A s.value, actions := [],
                      pending := [.valuePB
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 0⟩)] }
          | succ j =>
              have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                ⟨d, by rw [s.hparent]; exact hd⟩
              exact (ih hsrc)
      | wkSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
          rw [hsrc'] at hd
          by_cases hc : s.c ≤ i
          · obtain ⟨e', he'⟩ := exists_get?_insertAt_ge s.d hc hd
            have hsrc : Σ' d, s.target.ctx.get? (i + 1) = some d :=
              ⟨e', by rw [s.htarget]; exact he'⟩
            exact { (ih hsrc) with
                    provider := .wkView (ih hsrc).provider s.d s.c,
                    actions := (ih hsrc).actions ++ [.wkLift s.d s.c] }
          · obtain ⟨e', he'⟩ := exists_get?_insertAt_lt s.d (Nat.lt_of_not_le hc) hd
            have hsrc : Σ' d, s.target.ctx.get? i = some d :=
              ⟨e', by rw [s.htarget]; exact he'⟩
            exact { (ih hsrc) with
                    provider := .wkView (ih hsrc).provider s.d s.c,
                    actions := (ih hsrc).actions ++ [.wkLift s.d s.c] }
      | esubSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
          rw [hsrc'] at hd
          by_cases hc : i < s.j
          · obtain ⟨e', he'⟩ := exists_get?_substRemove_lt s.v hc hd
            have hsrc : Σ' d, s.target.ctx.get? i = some d :=
              ⟨e', by rw [s.htarget]; exact he'⟩
            exact { (ih hsrc) with
                    provider := .esubView (ih hsrc).provider s.Γ s.t s.j s.hget
                      (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                      (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                    actions := (ih hsrc).actions ++ [.esubAct s.j] }
          · by_cases heq : i = s.j
            · subst heq
              exact { occurrence := s.owner, origin := .ambientTransported,
                      family := .R, domRole := .ascribedType, termRole := .term,
                      provider := .original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩,
                      providerMap := (eval r').map,
                      valueRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                      typeRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                      valueRoute := some ⟨s.target, r'⟩,
                      entry := .assumption s.t, actions := [],
                      pending := [.providerAlign
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩)] }
            · have hgt : s.j < i := by omega
              obtain ⟨e', he'⟩ := exists_get?_substRemove_gt s.v hgt hd
              have hsrc : Σ' d, s.target.ctx.get? (i - 1) = some d :=
                ⟨e', by rw [s.htarget]; exact he'⟩
              exact { (ih hsrc) with
                      provider := .esubView (ih hsrc).provider s.Γ s.t s.j s.hget
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                      actions := (ih hsrc).actions ++ [.esubAct s.j] }
      | lsubSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
          rw [hsrc'] at hd
          by_cases hc : i < s.j
          · obtain ⟨e', he'⟩ := exists_get?_substRemove_lt s.v hc hd
            have hsrc : Σ' d, s.target.ctx.get? i = some d :=
              ⟨e', by rw [s.htarget]; exact he'⟩
            exact { (ih hsrc) with
                    provider := .lsubView (ih hsrc).provider s.Γ s.t s.v s.j s.hget
                      (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                      (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                    actions := (ih hsrc).actions ++ [.lsubAct s.j] }
          · by_cases heq : i = s.j
            · subst heq
              exact { occurrence := s.owner, origin := .ambientTransported,
                      family := .R, domRole := .ascribedType,
                      termRole := .storedValue,
                      provider := .original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩,
                      providerMap := (eval r').map,
                      valueRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                      typeRef := some
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                      valueRoute := some ⟨s.target, r'⟩,
                      entry := .letBinding s.t s.v, actions := [],
                      pending := [.valuePB
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩)] }
            · have hgt : s.j < i := by omega
              obtain ⟨e', he'⟩ := exists_get?_substRemove_gt s.v hgt hd
              have hsrc : Σ' d, s.target.ctx.get? (i - 1) = some d :=
                ⟨e', by rw [s.htarget]; exact he'⟩
              exact { (ih hsrc) with
                      provider := .lsubView (ih hsrc).provider s.Γ s.t s.v s.j s.hget
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 1⟩)
                        (.original ⟨s.owner.nodePath ++ [s.owner.field], 2⟩),
                      actions := (ih hsrc).actions ++ [.lsubAct s.j] }
      | linstSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
          rw [hsrc'] at hd
          have he : (instLvlsCtx s.ls s.Γ).get? i = some (instLvlsDecl s.ls d) := by
            have hd' : s.Γ[i]? = some d := by
              rwa [List.get?_eq_getElem?] at hd
            rw [instLvlsCtx, List.get?_eq_getElem?, List.getElem?_map, hd']
            rfl
          have hsrc : Σ' d, s.target.ctx.get? i = some d :=
            ⟨_, by rw [s.htarget]; exact he⟩
          exact { (ih hsrc) with
                  provider := .linstView (ih hsrc).provider s.ls,
                  actions := (ih hsrc).actions ++ [.linstAct s.ls] }
      | ewkSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc : Σ' d, s.target.ctx.get? i = some d :=
            ⟨d, by rw [s.htarget]; rw [s.hsource] at hd; exact hd⟩
          exact { (ih hsrc) with
                  provider := .ewkView (ih hsrc).provider s.owner s.hext
                    (.inl ⟨_, _, _, _, s.hext, TyP.toTyNode s.D, s.hpos⟩),
                  actions := (ih hsrc).actions ++ [.ewkAct] }
      | cctxSource s =>
          obtain ⟨d, hd⟩ := h
          have hsrc' : s.source.ctx = .assumption s.A :: s.Γ := by rw [s.hsource]
          rw [hsrc'] at hd
          have htgt : s.target.ctx = .assumption s.A' :: s.Γ := by rw [s.htarget]
          have hsrc : Σ' d, s.target.ctx.get? i = some d := by
            cases i with
            | zero => exact ⟨.assumption s.A', by simp [htgt]⟩
            | succ j =>
                have hd' : s.Γ.get? j = some d := by
                  simpa only [List.get?_cons_succ] using hd
                exact ⟨d, by
                  rw [htgt, List.get?_cons_succ]
                  exact hd'⟩
          exact { (ih hsrc) with
                  provider := .cctxView (ih hsrc).provider
                    ⟨s.owner.nodePath ++ [s.owner.field], 1⟩,
                  actions := (ih hsrc).actions ++ [.cctxAct] }
      | tail s =>
          obtain ⟨d, hd⟩ := h
          have hchild : s.child.ctx = s.Γ.drop s.k := by rw [s.hchild]
          rw [hchild, List.get?_eq_getElem?, List.getElem?_drop] at hd
          have hsrc : Σ' d, s.parent.ctx.get? (s.k + i) = some d :=
            ⟨d, by rw [s.hparent]; rwa [List.get?_eq_getElem?]⟩
          exact { (ih hsrc) with
                  actions := (ih hsrc).actions ++ [.tailMove s.k] }
      | admission s =>
          obtain ⟨d, hd⟩ := h
          have hstored : s.stored.ctx = ([] : LCtx) := by rw [s.hstored]
          rw [hstored] at hd
          simp at hd

/-- §2.2's `slotPlan`: the structural plan plus the verbatim resolve
    operation `(eval r).disp[i]?`. -/
noncomputable def slotPlan {F : RawForest} {p : Place} (r : DisplayRoute F p)
    {i : Nat} {A : Expr Nat} (hlook : lookupType p.ctx i = some A) :
    SlotPlan F r i A :=
  { toSlotData := slotDataOf r (get?_of_lookupType hlook),
    resolveOp := (eval r).disp[i]? }

/-- `resolveOp` is the actual disposition at `i`, by construction. -/
theorem slotPlan_resolve_op {F : RawForest} {p : Place} (r : DisplayRoute F p)
    {i : Nat} {A : Expr Nat} (hlook : lookupType p.ctx i = some A) :
    (slotPlan r hlook).resolveOp = (eval r).disp[i]? := rfl

/-! ## §2.2 — resolve algebra -/

/-- A lifted `ETm` is `★` iff the original was `★`. -/
theorem ETm.lift_eq_star {e : ETm} {c k : Nat} :
    e.lift c k = .star ↔ e = .star := by
  cases e <;> simp [ETm.lift]
  · rename_i i; by_cases hc : c ≤ i <;> simp [hc]

/-- `resolve ρ i` erases to `★` exactly when the disposition at position `i`
    is `drop` or `inline .star` — pure route algebra over `ρ[i]?`. -/
theorem resolve_star_iff_op (ρ : List Disp) (i : Nat) :
    (resolve ρ i = .star) ↔
      (match ρ[i]? with
       | some .drop => true
       | some (.inline .star) => true
       | _ => false) = true := by
  induction ρ generalizing i with
  | nil => simp [resolve]
  | cons d ρ ih =>
      cases i with
      | zero =>
          cases d with
          | keep => simp [resolve]
          | drop => simp [resolve]
          | inline v => cases v <;> simp [resolve]
      | succ i =>
          cases d with
          | keep =>
              simp only [resolve, List.getElem?_cons_succ]
              rw [ETm.lift_eq_star]
              exact ih i
          | drop =>
              simp only [resolve, List.getElem?_cons_succ]
              exact ih i
          | inline v =>
              simp only [resolve, List.getElem?_cons_succ]
              exact ih i

/-- §2.2's readback equation: the plan's computed `entryBit` is exactly the
    star status of `resolve (eval r).disp i` — an equation proved from the
    resolve operation, not a stored answer. -/
theorem slotPlan_resolve_star {F : RawForest} {p : Place} (r : DisplayRoute F p)
    {i : Nat} {A : Expr Nat} (hlook : lookupType p.ctx i = some A) :
    resolve (eval r).disp i = .star ↔ (slotPlan r hlook).entryBit = true := by
  show resolve (eval r).disp i = .star ↔
    (match (eval r).disp[i]? with
     | some .drop => true
     | some (.inline .star) => true
     | _ => false) = true
  exact resolve_star_iff_op _ _

/-! ## §2.5 — composition from the named answers -/

/-- §2.5 verbatim: with `b := plan.entryBit`, `hresolve` from
    `slotPlan_resolve_star`, the named `halign` (entry bit = `hA`'s mapped
    level bit) and the named `hBit` (`BitCoh σ hA DT`), compose
    `pbit_bvar_proof_reg` / `eps_bvar_rel` and `pbit_of_reg_and_bitCoh`.
    Consumes the answers; supplies neither. -/
theorem slotPlan_resolve_of_answers {F : RawForest} {p : Place}
    (r : DisplayRoute F p)
    {i : Nat} {A : Expr Nat} {u s : Level}
    (hlook : lookupType p.ctx i = some A)
    (hA : TyP p.env p.arity p.ctx A (.sort u))
    (DT : TyP p.env p.arity p.ctx A (.sort s))
    (halign : (slotPlan r hlook).entryBit = levelIsZero ((eval r).map u))
    (hBit : BitCoh (eval r).map hA DT) :
    PBit (eval r).map (eval r).disp
      (TyP.bvar p.env p.arity p.ctx i A u hlook hA) DT := by
  have hresolve := slotPlan_resolve_star r hlook
  have hreg : PBit (eval r).map (eval r).disp
      (TyP.bvar p.env p.arity p.ctx i A u hlook hA) hA := by
    cases hz : levelIsZero ((eval r).map u) with
    | true => exact pbit_bvar_proof_reg _ _ hlook hA hz
    | false =>
        unfold PBit
        rw [eps_bvar_rel hz, ← halign]
        exact hresolve
  exact pbit_of_reg_and_bitCoh _ DT hreg hBit

/-! ## §2.1 — the bvar's BitCoh request descends -/

/-- §2.1: `qBit = BitCoh σ hA DT` is strictly below the `TyP.bvar` PBit
    query — same original prefix length, strict `combMeas` descent by
    main's `combLexDM_pbit_bvar_sort` (`D.wt Aw = 1 + hA.wt Aw`). -/
theorem bvar_bit_request_below (Aw : Nat → Nat)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {i : Nat} {A : Expr Nat}
    {u s : Level}
    (S : ScopedCtx Eₐ E n Γ) (σ : Level → Level) (ρ : List Disp)
    (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
    (DT : TyP E n Γ A (.sort s)) :
    Before Aw
      (.bitCoh hA DT S σ ρ)
      (.pb (TyP.bvar E n Γ i A u hlook hA) DT S σ ρ) := by
  show KeyLT _ _
  apply Prod.Lex.right
  exact combLexDM_pbit_bvar_sort Aw
    (enrichCtxWfT_of_envWfT S.env S.ctx) hlook hA DT

/-! ## §2.3 — the ambient-let value PB descends -/

/-- §2.3: the value request `PB[hv₀, hA₀]` at the let's tail context `Γ₀` is
    strictly below the caller's PBit query at `Γ` — the prefix no longer
    read (`Γ.drop (i+1) = Γ₀`) is a strict descent in the rank's first
    component. Holds for every slot index `i` naming a `.letBinding` entry. -/
theorem slot_value_request_below (Aw : Nat → Nat)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ Γ₀ : LCtx} {i : Nat}
    {A₀ v₀ e T : Expr Nat} {u₀ s : Level}
    (S : ScopedCtx Eₐ E n Γ) (S₀ : ScopedCtx Eₐ E n Γ₀)
    (σ σ₀ : Level → Level) (ρ ρ₀ : List Disp)
    (hentry : Γ.get? i = some (.letBinding A₀ v₀))
    (hsub : Γ.drop (i + 1) = Γ₀)
    (hA₀ : TyP E n Γ₀ A₀ (.sort u₀)) (hv₀ : TyP E n Γ₀ v₀ A₀)
    (D : TyP E n Γ e T) (DT : TyP E n Γ T (.sort s)) :
    Before Aw (.pb hv₀ hA₀ S₀ σ₀ ρ₀) (.pb D DT S σ ρ) := by
  apply Prod.Lex.left
  show (P2Query.pb hv₀ hA₀ S₀ σ₀ ρ₀).originalPrefixLength <
    (P2Query.pb D DT S σ ρ).originalPrefixLength
  show Γ₀.length < Γ.length
  have he : Γ[i]? = some (LocalDecl.letBinding A₀ v₀) := by
    rwa [List.get?_eq_getElem?] at hentry
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.mp he
  rw [← hsub, List.length_drop]
  omega

/-- §2.3's index-0 composition: when the callee's original prefix has the
    entry sits at the head: the caller's scope enriches to the real
    `.letBinding` `CtxP` (`hS`) and the callee's scope enriches to its tail
    (`hS₀`). Descent is the first rank component — the let's tail drops the
    head entry, `Γ₀.length < (letBinding A₀ v₀ :: Γ₀).length`. -/
theorem slot_value_request_below_of_ctx (Aw : Nat → Nat)
    {Eₐ E : ResolvedEnv} {n : Nat} {Γ₀ : LCtx}
    {A₀ v₀ e T : Expr Nat} {u₀ s : Level}
    (S : ScopedCtx Eₐ E n (.letBinding A₀ v₀ :: Γ₀))
    (S₀ : ScopedCtx Eₐ E n Γ₀)
    (σ σ₀ : Level → Level) (ρ ρ₀ : List Disp)
    (C₀ : CtxP E n Γ₀) (hA₀ : TyP E n Γ₀ A₀ (.sort u₀)) (hv₀ : TyP E n Γ₀ v₀ A₀)
    (hS : enrichCtxWfT_of_envWfT S.env S.ctx =
      .letBinding E n Γ₀ A₀ u₀ v₀ C₀ hA₀ hv₀)
    (hS₀ : enrichCtxWfT_of_envWfT S₀.env S₀.ctx = C₀)
    (D : TyP E n (.letBinding A₀ v₀ :: Γ₀) e T)
    (DT : TyP E n (.letBinding A₀ v₀ :: Γ₀) T (.sort s)) :
    Before Aw (.pb hv₀ hA₀ S₀ σ₀ ρ₀) (.pb D DT S σ ρ) := by
  show KeyLT _ _
  apply Prod.Lex.left
  show (P2Query.pb hv₀ hA₀ S₀ σ₀ ρ₀).originalPrefixLength <
    (P2Query.pb D DT S σ ρ).originalPrefixLength
  show Γ₀.length < (LocalDecl.letBinding A₀ v₀ :: Γ₀).length
  simp

end Rcic.Syn
