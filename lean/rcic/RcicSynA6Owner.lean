import rcic.RcicSynRouteSlot
import rcic.RcicSynA6Link

/-!
# A6 — recovering the real owners: receipt selection and the route-event table

`BELOWC_A6_LINK_DECODER.md` §3 (ChatGPT J line, docs PR #7450), implemented on the landed
`DisplayRoute` layer (fable-step ITEM 6, 2026-10-17). `closure_claim = 0`.

Linkage (`RcicSynA6Link`) and ownership are separate tasks. Owner recovery walks the
actual context route back to the receipt, introduction or replacement that owns a slot,
keeping the event witnesses; no semantic answer selects a branch.

* `RootOwner` / `rootOwner` — **root receipt selection**: an indexed traversal of the
  actual `CtxP` receipt. At index `0` of an `assumption` node the owner is its domain
  field (family `K`); of a `letBinding` node its domain and value fields (family `V`);
  at a successor the traversal recurses into the tail receipt keeping the prefix
  continuation; an empty receipt contradicts the lookup. Provider addresses are
  receipt-field positions (`domAddr`/`valAddr`: tail is child `0`, domain child `1`,
  value child `2` of the receipt node), so equal proof values at different positions are
  different occurrences. `RootOwner.lookup` ties the selected domain to the actual
  lookup, `RootOwner.drop_eq` to the actual tail, `RootOwner.domAddr_at` /
  `RootOwner.valAddr_at` read the fields back at their addresses.
* `OwnerStep` / `OwnerRoute` — **the route-event table**: every landed `RouteEdge`
  (Na/Nl introductions by `assumeBody`/`letBody`, the `wk`/`esub`/`lsub`/`linst`/`ewk`/
  `cctx` sources, `tail`, `admission`), plus the two event families the landed grammar
  lacks — the ES Π/λ body (`CvAssumeBodySite`, pinned to the actual `CvP.pi`/`CvP.lam`
  node) and the ES let body (`CvLetBodySite`, the actual `CvP.letE` node) — and the
  projection events (`reg`/`dl`/`dr`/field: same place, address updated, route kept).
  `OwnerRoute.ofDisplayRoute` embeds every landed route.
* `ownerOf` — **total by induction on the finite route**: assumption/let bodies at slot
  `0` select the introducing domain (and value) field, successors recurse into the
  parent slot; ES bodies at slot `0` select the domain conversion's `dl` (and the value
  conversion's `dl`); `wk` maps the source index to the target index; `esub`/`lsub` at
  the cutoff select the node's own `Re`/`Rl` packet (`hvT`, `hv` — already at the target
  context), misses recurse at `i` or `i - 1`; `cctx` keeps the index and, at slot `0`,
  keeps the zero-slot bridge (`Bridge`); `linst`/`ewk` keep the index with their
  list/inclusion; `tail` by `k` recurses at `i + k`; an admission's empty stored context
  makes the lookup impossible. The pending transport-action stack (`PendingAction`,
  answer-free) is recorded in forward order.

The landed `slotDataOf` (`RcicSynRouteSlot`) keeps placeholder root owners (the root
site's own position for every slot). This module does not change it (the stack is
signed off); `rootOwnerAt` is the real entry selector it should call, and
`rootOwnerAt_lookup` is the contract. Not proven here: that `ownerOf ∘ ofDisplayRoute`
agrees with `slotDataOf` on `family`/`actions` (both are route recursions; the equation
is recorded, not claimed). Residues carried: W-A6-OWNER-REGISTRATION (CvP body /
projection events now registered; `slotDataOf.root` still placeholder),
W-A6-ACQUISITION-SCHEDULE (completion/retirement of owners is not built).
-/

namespace Rcic.Syn

open Rcic.Declarative

/-! ## §1 — root receipt selection on the actual `CtxP` receipt -/

/-- **The real owner of slot `i` of an actual context receipt** `hΓ : CtxP E n Γ`: the
    receipt node whose entry is `Γ[i]`, read as that node's own fields. `hereK`: an
    assumption at index `0` (family `K`, the domain field); `hereV`: a let at index `0`
    (family `V`, domain and value fields); `tailK`/`tailV`: a successor index recurses
    into the tail receipt. -/
inductive RootOwner (E : ResolvedEnv) (n : Nat) : {Γ : LCtx} → CtxP E n Γ → Nat → Type where
  | hereK {Γ : LCtx} {A : Expr Nat} {u : Level} (hΓ : CtxP E n Γ) (hA : TyP E n Γ A (.sort u)) :
      RootOwner E n (.assumption E n Γ A u hΓ hA) 0
  | hereV {Γ : LCtx} {A : Expr Nat} {u : Level} {v : Expr Nat} (hΓ : CtxP E n Γ)
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) :
      RootOwner E n (.letBinding E n Γ A u v hΓ hA hv) 0
  | tailK {Γ : LCtx} {A : Expr Nat} {u : Level} {hΓ : CtxP E n Γ} (hA : TyP E n Γ A (.sort u))
      {i : Nat} (o : RootOwner E n hΓ i) : RootOwner E n (.assumption E n Γ A u hΓ hA) (i + 1)
  | tailV {Γ : LCtx} {A : Expr Nat} {u : Level} {v : Expr Nat} {hΓ : CtxP E n Γ}
      (hA : TyP E n Γ A (.sort u)) (hv : TyP E n Γ v A) {i : Nat} (o : RootOwner E n hΓ i) :
      RootOwner E n (.letBinding E n Γ A u v hΓ hA hv) (i + 1)

/-- **Root receipt selection is total**: a successful entry read selects the owner; the
    empty receipt contradicts the read. -/
def rootOwner {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → (hΓ : CtxP E n Γ) → (i : Nat) → (∃ d, Γ.get? i = some d) → RootOwner E n hΓ i
  | _, .nil _ _, _, h => absurd h (by simp)
  | _, .assumption _ _ _ _ _ hΓ hA, 0, _ => .hereK hΓ hA
  | _, .assumption _ _ _ _ _ hΓ hA, i + 1, h =>
      .tailK hA (rootOwner hΓ i (by simpa using h))
  | _, .letBinding _ _ _ _ _ _ hΓ hA hv, 0, _ => .hereV hΓ hA hv
  | _, .letBinding _ _ _ _ _ _ hΓ hA hv, i + 1, h =>
      .tailV hA hv (rootOwner hΓ i (by simpa using h))

/-- The selected entry's origin family: `K` for an assumption, `V` for a stored let. -/
def RootOwner.family {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → RootOwner E n hΓ i → OriginFamily
  | _, _, _, .hereK _ _ => .K
  | _, _, _, .hereV _ _ _ => .V
  | _, _, _, .tailK _ o => RootOwner.family o
  | _, _, _, .tailV _ _ o => RootOwner.family o

/-- The receipt-field address of the selected domain field: tail child `0` at every
    successor, domain child `1` at the entry. -/
def RootOwner.domAddr {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → RootOwner E n hΓ i → List Nat
  | _, _, _, .hereK _ _ => [1]
  | _, _, _, .hereV _ _ _ => [1]
  | _, _, _, .tailK _ o => 0 :: RootOwner.domAddr o
  | _, _, _, .tailV _ _ o => 0 :: RootOwner.domAddr o

/-- The receipt-field address of the selected value field (`some` only for a let entry:
    value child `2`). -/
def RootOwner.valAddr {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → RootOwner E n hΓ i → Option (List Nat)
  | _, _, _, .hereK _ _ => none
  | _, _, _, .hereV _ _ _ => some [2]
  | _, _, _, .tailK _ o => (RootOwner.valAddr o).map (0 :: ·)
  | _, _, _, .tailV _ _ o => (RootOwner.valAddr o).map (0 :: ·)

/-- The selected fields: the tail receipt, the domain field `I`, and the value field
    `V` when the entry is a let. -/
structure RootSel (E : ResolvedEnv) (n : Nat) : Type where
  {Γ' : LCtx} {A : Expr Nat} {u : Level}
  tail : CtxP E n Γ'
  dom : TyP E n Γ' A (.sort u)
  value : Option (Σ' v : Expr Nat, TyP E n Γ' v A)

/-- Read the selected fields off the receipt node. -/
def RootOwner.sel {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → RootOwner E n hΓ i → RootSel E n
  | _, _, _, .hereK hΓ hA => ⟨hΓ, hA, none⟩
  | _, _, _, .hereV hΓ hA hv => ⟨hΓ, hA, some ⟨_, hv⟩⟩
  | _, _, _, .tailK _ o => RootOwner.sel o
  | _, _, _, .tailV _ _ o => RootOwner.sel o

/-- The selected tail is the receipt's context after the entry. -/
theorem RootOwner.drop_eq {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → (o : RootOwner E n hΓ i) →
      Γ.drop (i + 1) = o.sel.Γ'
  | _, _, _, .hereK _ _ => rfl
  | _, _, _, .hereV _ _ _ => rfl
  | _, _, _, .tailK _ o => RootOwner.drop_eq o
  | _, _, _, .tailV _ _ o => RootOwner.drop_eq o

/-- **The selected domain IS the lookup**: `lookupType Γ i = some (lift 0 (i+1) A)` for
    the selected entry's stored type `A` (the tail lookups compose with the 0-cutoff lift,
    `lookupType_cons_succ` + `lift_lift_merge`). -/
theorem RootOwner.lookup {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → (o : RootOwner E n hΓ i) →
      lookupType Γ i = some (lift 0 (i + 1) o.sel.A)
  | _, _, _, .hereK _ _ => rfl
  | _, _, _, .hereV _ _ _ => rfl
  | _, _, _, .tailK (i := i) _ o => by
      show lookupType _ (i + 1) = some (lift 0 (i + 1 + 1) o.sel.A)
      rw [lookupType_cons_succ, RootOwner.lookup o, Option.map_some',
        lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _)]
  | _, _, _, .tailV (i := i) _ _ o => by
      show lookupType _ (i + 1) = some (lift 0 (i + 1 + 1) o.sel.A)
      rw [lookupType_cons_succ, RootOwner.lookup o, Option.map_some',
        lift_lift_merge 1 (i + 1) 0 0 (Nat.le_refl 0) (Nat.zero_le _)]

/-- A let entry selects a value field exactly when the family is `V`. -/
theorem RootOwner.value_isSome {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → (o : RootOwner E n hΓ i) →
      o.sel.value.isSome = (o.family = .V : Bool)
  | _, _, _, .hereK _ _ => rfl
  | _, _, _, .hereV _ _ _ => rfl
  | _, _, _, .tailK _ o => RootOwner.value_isSome o
  | _, _, _, .tailV _ _ o => RootOwner.value_isSome o

/-! The receipt node's children: tail at `0`, domain at `1`, value at `2`. -/

theorem at_ctx_assumption_tail {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} (p : List Nat) :
    (RawForest.ctx (CtxP.toCtxNode (.assumption E n Γ A u hΓ hA))).at (0 :: p) =
      (RawForest.ctx hΓ.toCtxNode).at p := rfl

theorem at_ctx_assumption_dom {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
    {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} (p : List Nat) :
    (RawForest.ctx (CtxP.toCtxNode (.assumption E n Γ A u hΓ hA))).at (1 :: p) =
      (RawForest.ty hA.toTyNode).at p := rfl

theorem at_ctx_letBinding_tail {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat}
    {u : Level} {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ v A}
    (p : List Nat) :
    (RawForest.ctx (CtxP.toCtxNode (.letBinding E n Γ A u v hΓ hA hv))).at (0 :: p) =
      (RawForest.ctx hΓ.toCtxNode).at p := rfl

theorem at_ctx_letBinding_dom {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat}
    {u : Level} {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ v A}
    (p : List Nat) :
    (RawForest.ctx (CtxP.toCtxNode (.letBinding E n Γ A u v hΓ hA hv))).at (1 :: p) =
      (RawForest.ty hA.toTyNode).at p := rfl

theorem at_ctx_letBinding_value {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A v : Expr Nat}
    {u : Level} {hΓ : CtxP E n Γ} {hA : TyP E n Γ A (.sort u)} {hv : TyP E n Γ v A}
    (p : List Nat) :
    (RawForest.ctx (CtxP.toCtxNode (.letBinding E n Γ A u v hΓ hA hv))).at (2 :: p) =
      (RawForest.ty hv.toTyNode).at p := rfl

/-- **The domain address reads the selected domain field** of the receipt's forest
    image. -/
theorem RootOwner.domAddr_at {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → (o : RootOwner E n hΓ i) →
      (RawForest.ctx hΓ.toCtxNode).at o.domAddr = some (.ty o.sel.dom.toTyNode)
  | _, _, _, .hereK _ _ => at_ctx_assumption_dom []
  | _, _, _, .hereV _ _ _ => at_ctx_letBinding_dom []
  | _, _, _, .tailK _ o => by
      show (RawForest.ctx _).at (0 :: o.domAddr) = some (.ty o.sel.dom.toTyNode)
      rw [at_ctx_assumption_tail]
      exact RootOwner.domAddr_at o
  | _, _, _, .tailV _ _ o => by
      show (RawForest.ctx _).at (0 :: o.domAddr) = some (.ty o.sel.dom.toTyNode)
      rw [at_ctx_letBinding_tail]
      exact RootOwner.domAddr_at o

/-- **The value address reads the selected value field** (when there is one). -/
theorem RootOwner.valAddr_at {E : ResolvedEnv} {n : Nat} :
    {Γ : LCtx} → {hΓ : CtxP E n Γ} → {i : Nat} → (o : RootOwner E n hΓ i) →
      ∀ q, o.valAddr = some q → ∃ (v : Expr Nat) (hv : TyP E n o.sel.Γ' v o.sel.A),
        o.sel.value = some ⟨v, hv⟩ ∧ (RawForest.ctx hΓ.toCtxNode).at q = some (.ty hv.toTyNode)
  | _, _, _, .hereK _ _, _, hq => by simp [RootOwner.valAddr] at hq
  | _, _, _, .hereV _ _ hv, q, hq => by
      simp only [RootOwner.valAddr, Option.some.injEq] at hq
      subst hq
      exact ⟨_, hv, rfl, at_ctx_letBinding_value []⟩
  | _, _, _, .tailK _ o, q, hq => by
      simp only [RootOwner.valAddr, Option.map_eq_some'] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨v, hv, hval, hat⟩ := RootOwner.valAddr_at o q' hq'
      exact ⟨v, hv, hval, by rw [at_ctx_assumption_tail]; exact hat⟩
  | _, _, _, .tailV _ _ o, q, hq => by
      simp only [RootOwner.valAddr, Option.map_eq_some'] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      obtain ⟨v, hv, hval, hat⟩ := RootOwner.valAddr_at o q' hq'
      exact ⟨v, hv, hval, by rw [at_ctx_letBinding_tail]; exact hat⟩

/-! ## §2 — the route-event table -/

/-- Where an owner's provider typings sit: inside the root receipt (receipt-relative
    addresses) or at forest field positions. -/
inductive OwnerAddr (F : RawForest) : Type where
  | receipt (dom : List Nat) (value : Option (List Nat))
  | forest (dom : FieldPath F) (value : Option (FieldPath F))

/-- A projection event: same place, the projection address changes, the route is kept. -/
inductive ProjRole : Type where
  | reg | dl | dr
  | field (k : Nat)
  deriving DecidableEq

/-- **The recovered owner of a slot**: the real provider typings (the domain field `I`,
    the stored value `V` when there is one), the origin family, the address of the
    fields, the pending transport-action stack in forward order, the zero-slot `cctx`
    bridges kept on the way, and the projections crossed. -/
structure Owner (F : RawForest) : Type where
  family : OriginFamily
  addr : OwnerAddr F
  {E : ResolvedEnv} {n : Nat} {Γ' : LCtx} {A : Expr Nat} {u : Level}
  dom : TyP E n Γ' A (.sort u)
  value : Option (Σ' v : Expr Nat, TyP E n Γ' v A)
  actions : List PendingAction
  bridges : List Bridge
  projs : List ProjRole

/-- The root owner as an `Owner`: the receipt's own selected fields, no pending
    actions. -/
noncomputable def rootOwnerAt {F : RawForest} (s : RootSite F) (i : Nat)
    (h : ∃ d, s.Γ.get? i = some d) : Owner F :=
  let o := rootOwner (enrichCtxWfT_of_envWfT s.S.env s.S.ctx) i h
  { family := o.family, addr := .receipt o.domAddr o.valAddr,
    dom := o.sel.dom, value := o.sel.value, actions := [], bridges := [], projs := [] }

/-- The root owner's contract: its domain field is the slot's actual lookup. -/
theorem rootOwnerAt_lookup {F : RawForest} (s : RootSite F) (i : Nat)
    (h : ∃ d, s.Γ.get? i = some d) :
    lookupType s.Γ i = some (lift 0 (i + 1) (rootOwnerAt s i h).A) :=
  RootOwner.lookup (rootOwner (enrichCtxWfT_of_envWfT s.S.env s.S.ctx) i h)

/-- The actual ES binder-parent payload: the real `CvP.pi` or `CvP.lam` constructor with
    its own domain conversion, body conversion and endpoints — never an arbitrary `CvP`. -/
inductive CvAssumeBodyParent (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Type where
  | pi (A A' B B' : Expr Nat) (u v : Level)
      (hA : CvP E n Γ A A' (.sort u)) (hB : CvP E n (.assumption A :: Γ) B B' (.sort v))
      (dl : TyP E n Γ (.pi A B) (.sort (.imax u v)))
      (dr : TyP E n Γ (.pi A' B') (.sort (.imax u v)))
  | lam (A A' b b' B : Expr Nat) (u : Level)
      (hA : CvP E n Γ A A' (.sort u)) (hb : CvP E n (.assumption A :: Γ) b b' B)
      (dl : TyP E n Γ (.lam A b) (.pi A B)) (dr : TyP E n Γ (.lam A' b') (.pi A B))

/-- The binder's left domain. -/
def CvAssumeBodyParent.A {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    CvAssumeBodyParent E n Γ → Expr Nat
  | .pi A _ _ _ _ _ _ _ _ _ | .lam A _ _ _ _ _ _ _ _ _ => A

/-- The binder's right domain. -/
def CvAssumeBodyParent.A' {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    CvAssumeBodyParent E n Γ → Expr Nat
  | .pi _ A' _ _ _ _ _ _ _ _ | .lam _ A' _ _ _ _ _ _ _ _ => A'

/-- The domain conversion's sort. -/
def CvAssumeBodyParent.u {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    CvAssumeBodyParent E n Γ → Level
  | .pi _ _ _ _ u _ _ _ _ _ | .lam _ _ _ _ _ u _ _ _ _ => u

/-- The parent's real domain-conversion field. -/
def CvAssumeBodyParent.hA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (p : CvAssumeBodyParent E n Γ) → CvP E n Γ p.A p.A' (.sort p.u)
  | .pi _ _ _ _ _ _ hA _ _ _ => hA
  | .lam _ _ _ _ _ _ hA _ _ _ => hA

/-- The parent conversion rebuilt from the payload's own fields. -/
def CvAssumeBodyParent.cv {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    CvAssumeBodyParent E n Γ → Σ' (a b T : Expr Nat), CvP E n Γ a b T
  | .pi A A' B B' u v hA hB dl dr => ⟨_, _, _, .pi E n Γ A A' B B' u v hA hB dl dr⟩
  | .lam A A' b b' B u hA hb dl dr => ⟨_, _, _, .lam E n Γ A A' b b' B u hA hb dl dr⟩

/-- ES Π/λ body event site: the actual `CvP.pi`/`CvP.lam` node, pinned by `hpos` to the
    node rebuilt from exactly its payload; the child place is the body's context
    `A :: Γ` (the LEFT domain, as the `hB`/`hb` field is typed). -/
structure CvAssumeBodySite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  payload : CvAssumeBodyParent E n Γ
  hpos : owner.node = some (.cv (CvP.toCvNode payload.cv.2.2.2))
  parent : Place
  child : Place
  hparent : parent = { env := E, arity := n, ctx := Γ }
  hchild : child = { env := E, arity := n, ctx := .assumption payload.A :: Γ }

/-- ES let body event site: the actual `CvP.letE` node's complete payload. -/
structure CvLetBodySite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A A' v v' b b' B : Expr Nat} {u : Level}
  hA : CvP E n Γ A A' (.sort u)
  hv : CvP E n Γ v v' A
  hb : CvP E n (.letBinding A v :: Γ) b b' B
  dl : TyP E n Γ (.letE A v b) (instantiate0 v B)
  dr : TyP E n Γ (.letE A' v' b') (instantiate0 v B)
  hpos : owner.node = some (.cv (CvP.toCvNode (.letE E n Γ A A' v v' b b' B u hA hv hb dl dr)))
  parent : Place
  child : Place
  hparent : parent = { env := E, arity := n, ctx := Γ }
  hchild : child = { env := E, arity := n, ctx := .letBinding A v :: Γ }

/-- **The route-event table**: one landed `RouteEdge`, an ES binder body, an ES let
    body, or a projection (same place). -/
inductive OwnerStep (F : RawForest) : Place → Place → Type where
  | edge {p q : Place} (e : RouteEdge F p q) : OwnerStep F p q
  | cvAssumeBody (s : CvAssumeBodySite F) : OwnerStep F s.parent s.child
  | cvLetBody (s : CvLetBodySite F) : OwnerStep F s.parent s.child
  | proj {p : Place} (role : ProjRole) : OwnerStep F p p

/-- An owner route: the root site plus a finite spine of route events. -/
inductive OwnerRoute (F : RawForest) : Place → Type where
  | root (s : RootSite F) : OwnerRoute F s.place
  | step {p q : Place} : OwnerRoute F p → OwnerStep F p q → OwnerRoute F q

/-- Every landed display route is an owner route. -/
def OwnerRoute.ofDisplayRoute {F : RawForest} : {p : Place} → DisplayRoute F p → OwnerRoute F p
  | _, .root s => .root s
  | _, .step r e => .step (OwnerRoute.ofDisplayRoute r) (.edge e)

/-! ## §3 — owner recovery, total by induction on the finite route -/

/-- **Owner recovery.** Walk the route's last event, map the slot index back to the
    previous place's index (or read the event's own payload when the event introduced
    or replaced the entry), and collect the real owner with its event witnesses. -/
noncomputable def ownerOf {F : RawForest} {p : Place} (r : OwnerRoute F p)
    {i : Nat} (h : Σ' d, p.ctx.get? i = some d) : Owner F := by
  induction r generalizing i with
  | root s =>
      obtain ⟨d, hd⟩ := h
      have hctx : s.place.ctx = s.Γ := by rw [s.hplace]
      rw [hctx] at hd
      exact rootOwnerAt s i ⟨d, hd⟩
  | step r' e ih =>
      cases e with
      | edge e =>
          cases e with
          | assumeBody s =>
              obtain ⟨d, hd⟩ := h
              have hchild : s.child.ctx = .assumption s.payload.A :: s.Γ := by rw [s.hchild]
              rw [hchild] at hd
              cases i with
              | zero =>
                  exact { family := .N,
                          addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 0⟩ none,
                          dom := s.payload.hA, value := none,
                          actions := [], bridges := [], projs := [] }
              | succ j =>
                  have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                    ⟨d, by rw [s.hparent]; exact hd⟩
                  exact ih hsrc
          | letBody s =>
              obtain ⟨d, hd⟩ := h
              have hchild : s.child.ctx = .letBinding s.A s.value :: s.Γ := by rw [s.hchild]
              rw [hchild] at hd
              cases i with
              | zero =>
                  exact { family := .N,
                          addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 0⟩
                            (some ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                          dom := s.hA, value := some ⟨s.value, s.hv⟩,
                          actions := [], bridges := [], projs := [] }
              | succ j =>
                  have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                    ⟨d, by rw [s.hparent]; exact hd⟩
                  exact ih hsrc
          | wkSource s =>
              obtain ⟨d, hd⟩ := h
              have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
              rw [hsrc'] at hd
              by_cases hc : s.c ≤ i
              · obtain ⟨e', he'⟩ := exists_get?_insertAt_ge s.d hc hd
                have hsrc : Σ' d, s.target.ctx.get? (i + 1) = some d :=
                  ⟨e', by rw [s.htarget]; exact he'⟩
                exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.wkLift s.d s.c] }
              · obtain ⟨e', he'⟩ := exists_get?_insertAt_lt s.d (Nat.lt_of_not_le hc) hd
                have hsrc : Σ' d, s.target.ctx.get? i = some d :=
                  ⟨e', by rw [s.htarget]; exact he'⟩
                exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.wkLift s.d s.c] }
          | esubSource s =>
              obtain ⟨d, hd⟩ := h
              have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
              rw [hsrc'] at hd
              by_cases hc : i < s.j
              · obtain ⟨e', he'⟩ := exists_get?_substRemove_lt s.v hc hd
                have hsrc : Σ' d, s.target.ctx.get? i = some d :=
                  ⟨e', by rw [s.htarget]; exact he'⟩
                exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.esubAct s.j] }
              · by_cases heq : i = s.j
                · exact { family := .R,
                          addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 2⟩
                            (some ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                          dom := s.hvT, value := some ⟨lift 0 s.j s.v, s.hv⟩,
                          actions := [], bridges := [], projs := [] }
                · have hgt : s.j < i := by omega
                  obtain ⟨e', he'⟩ := exists_get?_substRemove_gt s.v hgt hd
                  have hsrc : Σ' d, s.target.ctx.get? (i - 1) = some d :=
                    ⟨e', by rw [s.htarget]; exact he'⟩
                  exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.esubAct s.j] }
          | lsubSource s =>
              obtain ⟨d, hd⟩ := h
              have hsrc' : s.source.ctx = s.Γ := by rw [s.hsource]
              rw [hsrc'] at hd
              by_cases hc : i < s.j
              · obtain ⟨e', he'⟩ := exists_get?_substRemove_lt s.v hc hd
                have hsrc : Σ' d, s.target.ctx.get? i = some d :=
                  ⟨e', by rw [s.htarget]; exact he'⟩
                exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.lsubAct s.j] }
              · by_cases heq : i = s.j
                · exact { family := .R,
                          addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 2⟩
                            (some ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                          dom := s.hvT, value := some ⟨lift 0 s.j s.v, s.hv⟩,
                          actions := [], bridges := [], projs := [] }
                · have hgt : s.j < i := by omega
                  obtain ⟨e', he'⟩ := exists_get?_substRemove_gt s.v hgt hd
                  have hsrc : Σ' d, s.target.ctx.get? (i - 1) = some d :=
                    ⟨e', by rw [s.htarget]; exact he'⟩
                  exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.lsubAct s.j] }
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
              exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.linstAct s.ls] }
          | ewkSource s =>
              obtain ⟨d, hd⟩ := h
              have hsrc : Σ' d, s.target.ctx.get? i = some d :=
                ⟨d, by rw [s.htarget]; rw [s.hsource] at hd; exact hd⟩
              exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.ewkAct] }
          | cctxSource s =>
              obtain ⟨d, hd⟩ := h
              have hsrc' : s.source.ctx = .assumption s.A :: s.Γ := by rw [s.hsource]
              rw [hsrc'] at hd
              have htgt : s.target.ctx = .assumption s.A' :: s.Γ := by rw [s.htarget]
              cases i with
              | zero =>
                  have hsrc : Σ' d, s.target.ctx.get? 0 = some d :=
                    ⟨.assumption s.A', by rw [htgt]; rfl⟩
                  exact { (ih hsrc) with
                          actions := (ih hsrc).actions ++ [.cctxAct],
                          bridges := (ih hsrc).bridges ++
                            [⟨s.hA, s.owner.nodePath ++ [s.owner.field, 1]⟩] }
              | succ j =>
                  have hd' : s.Γ.get? j = some d := by
                    simpa only [List.get?_cons_succ] using hd
                  have hsrc : Σ' d, s.target.ctx.get? (j + 1) = some d :=
                    ⟨d, by rw [htgt, List.get?_cons_succ]; exact hd'⟩
                  exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.cctxAct] }
          | tail s =>
              obtain ⟨d, hd⟩ := h
              have hchild : s.child.ctx = s.Γ.drop s.k := by rw [s.hchild]
              rw [hchild, List.get?_eq_getElem?, List.getElem?_drop] at hd
              have hsrc : Σ' d, s.parent.ctx.get? (s.k + i) = some d :=
                ⟨d, by rw [s.hparent]; rwa [List.get?_eq_getElem?]⟩
              exact { (ih hsrc) with actions := (ih hsrc).actions ++ [.tailMove s.k] }
          | admission s =>
              obtain ⟨d, hd⟩ := h
              have hstored : s.stored.ctx = ([] : LCtx) := by rw [s.hstored]
              rw [hstored] at hd
              simp at hd
      | cvAssumeBody s =>
          obtain ⟨d, hd⟩ := h
          have hchild : s.child.ctx = .assumption s.payload.A :: s.Γ := by rw [s.hchild]
          rw [hchild] at hd
          cases i with
          | zero =>
              exact { family := .N,
                      addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 0⟩ none,
                      dom := s.payload.hA.dl, value := none,
                      actions := [], bridges := [], projs := [] }
          | succ j =>
              have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                ⟨d, by rw [s.hparent]; exact hd⟩
              exact ih hsrc
      | cvLetBody s =>
          obtain ⟨d, hd⟩ := h
          have hchild : s.child.ctx = .letBinding s.A s.v :: s.Γ := by rw [s.hchild]
          rw [hchild] at hd
          cases i with
          | zero =>
              exact { family := .N,
                      addr := .forest ⟨s.owner.nodePath ++ [s.owner.field], 0⟩
                        (some ⟨s.owner.nodePath ++ [s.owner.field], 1⟩),
                      dom := s.hA.dl, value := some ⟨s.v, s.hv.dl⟩,
                      actions := [], bridges := [], projs := [] }
          | succ j =>
              have hsrc : Σ' d, s.parent.ctx.get? j = some d :=
                ⟨d, by rw [s.hparent]; exact hd⟩
              exact ih hsrc
      | proj role =>
          exact { (ih h) with projs := (ih h).projs ++ [role] }

/-- A root site's place reads its own scope: the entry read, moved to `s.Γ`. -/
theorem RootSite.entryScope {F : RawForest} (s : RootSite F) {i : Nat}
    (h : Σ' d, s.place.ctx.get? i = some d) : ∃ d, s.Γ.get? i = some d := by
  obtain ⟨d, hd⟩ := h
  have hctx : s.place.ctx = s.Γ := by rw [s.hplace]
  rw [hctx] at hd
  exact ⟨d, hd⟩

/-- At the root, owner recovery IS root receipt selection. -/
theorem ownerOf_root {F : RawForest} (s : RootSite F) {i : Nat}
    (h : Σ' d, s.place.ctx.get? i = some d) :
    ownerOf (.root s) h = rootOwnerAt s i (s.entryScope h) := by
  obtain ⟨d, hd⟩ := h
  rfl

end Rcic.Syn
