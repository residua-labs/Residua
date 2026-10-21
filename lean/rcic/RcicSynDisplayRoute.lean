import rcic.RcicSynBelowCFix
import rcic.RcicSynPack
import rcic.RcicSynErase
import rcic.RcicERLocalize

/-!
# S16 — `DisplayRoute` as a concrete datatype (§1–§3)

`research/rcic/sortrow/S16_DISPLAY_ROUTE_DATATYPE.md` (ChatGPT S16, #7384)
over the p-auth shared layer: `RawForest` positions (`FieldPath`), derived
references (`DRef`), display places (`Place`), the ten `*Site` records plus
`RootSite`, `RouteEdge`/`DisplayRoute`, and the computed `eval` — one defining
equation per edge, exactly the §3 table. `closure_claim = 0`.

Two data layers, kept apart per §1:

- **Original position layer.** `FieldPath F` is an ordered position in the
  root forest — a children-path plus a constructor-field index. Positions are
  indexed, not looked up by value: `refl`'s `h`/`dl`/`dr` are three different
  `FieldPath`s even when the payloads they name are equal.
- **Derived reference layer.** `DRef` names a deterministic, recomputed view;
  `.val` is a partial deterministic projection — a reference that cannot be
  read back is `none`, never fabricated into an "original leaf".

Every `*Site` carries the original owner/field position, the constructor's
complete real payload (the original `TyP`/`CvP` fields), the "node rebuilt
from the payload = node read at that position" equation `hpos`, and
componentwise `Place` equations. A site stitched from two different nodes
fails `hpos`: `esubSite_node_forced` shows the node at the owner position is
exactly the one rebuilt from the site's own payload.
-/

namespace Rcic.Syn

open Rcic.Declarative

-- `localize` is imported from `rcic.RcicERLocalize` (the landed #7374 — the
-- S16 spec's `lsubSource` inserts `inline (localize κ rV)` with that def).

/-! ## §1 — positions and derived references -/

/-- An ordered position in the root forest `F`: `nodePath` descends through
    `children` indices, `field` names the constructor-field slot. Two equal
    payloads at different `(nodePath, field)` pairs are different positions. -/
structure FieldPath (F : RawForest) : Type where
  nodePath : List Nat
  field : Nat
  deriving DecidableEq, Repr

/-- The node a children-path points at (`none` when it runs off the tree). -/
def RawForest.at (F : RawForest) : List Nat → Option RawForest
  | [] => some F
  | i :: p => do let c ← F.children[i]?; c.at p

/-- The node a `FieldPath` reads: the occupant of the selected field slot —
    `children[field]` of the node at `nodePath`. Never the container node
    itself. -/
def FieldPath.node {F : RawForest} (p : FieldPath F) : Option RawForest :=
  (F.at p.nodePath).bind (·.children[p.field]?)

/-- §1's derived-reference grammar. `reg`/`dl`/`dr`-style references carry
    their own bounds (the path or levels they name) and are never registered
    as new original leaves. -/
inductive DRef (F : RawForest) : Type where
  | original (p : FieldPath F)
  | reg (p : FieldPath F)
  | dl (p : FieldPath F)
  | dr (p : FieldPath F)
  | sortNode (E : ResolvedEnv) (n : Nat) (Γ : LCtx) (e s : Expr Nat)
  | wkView (ref : DRef F) (d : LocalDecl) (c : Nat)
  | esubView (ref : DRef F) (Γ : LCtx) (t : Expr Nat) (j : Nat)
      (hget : Γ[j]? = some (.assumption t)) (hv hvT : DRef F)
  | lsubView (ref : DRef F) (Γ : LCtx) (t v : Expr Nat) (j : Nat)
      (hget : Γ[j]? = some (.letBinding t v)) (hv hvT : DRef F)
  | linstView (ref : DRef F) (ls : List Level)
  | ewkView (ref : DRef F) (pos : FieldPath F) {E₀ E : ResolvedEnv}
      (hext : EnvExt E₀ E)
      (hbound : (∃ (n : Nat) (Γ : LCtx) (e A : Expr Nat) (hext' : EnvExt E₀ E)
          (D : TyNode E₀ n Γ e A),
          pos.node = some (.ty (.ewk E₀ E n Γ e A hext' D)))
        ∨ (∃ (n : Nat) (Γ : LCtx) (a b T : Expr Nat) (hext' : EnvExt E₀ E)
          (h : CvNode E₀ n Γ a b T),
          pos.node = some (.cv (.ewk E₀ E n Γ a b T hext' h))))
  | cctxView (ref : DRef F) (bridge : FieldPath F)
  | indexCast {e e' : Expr Nat} (he : e = e')
  | admissionRead (p : FieldPath F)

/-- Node-level left typing endpoint — `CvP.dl` verbatim on `CvNode`:
    stored `dl` fields are read; transport nodes re-transport the inner
    endpoint, exactly as `CvP.dl` does. -/
def CvNode.dl : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvNode E n Γ a b T → TyNode E n Γ a T
  | _, _, _, _, _, _, .refl _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ _ _ _ dl _ => dl
  | _, _, _, _, _, _, .wk E n Γ a _ T d c h => .wk E n Γ a T d c h.dl
  | _, _, _, _, _, _, .esub E n Γ a _ T t v j u h hget hv hvT =>
      .esub E n Γ a T t v j u h.dl hget hv hvT
  | _, _, _, _, _, _, .linst E a' n Γ a _ T ls hls hlen h =>
      .linst E a' n Γ a T ls hls hlen h.dl
  | _, _, _, _, _, _, .ewk E₀ E n Γ a _ T hext h => .ewk E₀ E n Γ a T hext h.dl
  | _, _, _, _, _, _, .cctx E n Γ a _ T A A' u h hA =>
      .cctx E n Γ a T A A' u h.dl hA

/-- Node-level right typing endpoint — `CvP.dr` verbatim on `CvNode`. -/
def CvNode.dr : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {a b T : Expr Nat} →
    CvNode E n Γ a b T → TyNode E n Γ b T
  | _, _, _, _, _, _, .refl _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .symm _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .trans _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .beta _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .zeta _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .zetaLocal _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .delta _ _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .iota _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .lit _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .app _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .lam _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .pi _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .letE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .sorts _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .consts _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .eta _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .irr _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .tyConv _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .fsub _ _ _ _ _ _ _ _ _ _ _ _ _ dr => dr
  | _, _, _, _, _, _, .wk E n Γ _ b T d c h => .wk E n Γ b T d c h.dr
  | _, _, _, _, _, _, .esub E n Γ _ b T t v j u h hget hv hvT =>
      .esub E n Γ b T t v j u h.dr hget hv hvT
  | _, _, _, _, _, _, .linst E a' n Γ _ b T ls hls hlen h =>
      .linst E a' n Γ b T ls hls hlen h.dr
  | _, _, _, _, _, _, .ewk E₀ E n Γ _ b T hext h => .ewk E₀ E n Γ b T hext h.dr
  | _, _, _, _, _, _, .cctx E n Γ _ b T A A' u h hA =>
      .cctx E n Γ b T A A' u h.dr hA

/-- Node-level regularity endpoint — `TyP.reg` verbatim on `TyNode`. -/
def TyNode.reg : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} → {e T : Expr Nat} →
    TyNode E n Γ e T → (u : Level) × TyNode E n Γ T (.sort u)
  | _, _, _, _, _, .sort E n Γ _ k _ => ⟨.succ k, .sort E n Γ k (.succ k) (eqN_refl _)⟩
  | _, _, _, _, _, .bvar _ _ _ _ _ u _ hA => ⟨u, hA⟩
  | _, _, _, _, _, .const _ _ _ _ _ _ _ u _ _ _ _ hT => ⟨u, hT⟩
  | _, _, _, _, _, .pi E n Γ _ u _ v _ _ =>
      ⟨.succ (.imax u v), .sort E n Γ (.imax u v) (.succ (.imax u v)) (eqN_refl _)⟩
  | _, _, _, _, _, .lam E n Γ A u _ B v hA _ hB => ⟨.imax u v, .pi E n Γ A u B v hA hB⟩
  | _, _, _, _, _, .app _ _ _ _ _ _ _ w _ _ hT => ⟨w, hT⟩
  | _, _, _, _, _, .letE _ _ _ _ _ _ _ _ w _ _ _ hT => ⟨w, hT⟩
  | _, _, _, _, _, .lit _ _ _ _ _ hexp => hexp.reg
  | _, _, _, _, _, .conv _ _ _ _ _ _ u _ hc => ⟨u, hc.dr⟩
  | _, _, _, _, _, .wk E n Γ _ A d c D =>
      let R := D.reg
      ⟨R.1, .wk E n Γ A (.sort R.1) d c R.2⟩
  | _, _, _, _, _, .esub E n Γ _ A t v j u D hget hv hvT =>
      let R := D.reg
      ⟨R.1, .esub E n Γ A (.sort R.1) t v j u R.2 hget hv hvT⟩
  | _, _, _, _, _, .lsub E n Γ _ A t v j u D hget hv hvT =>
      let R := D.reg
      ⟨R.1, .lsub E n Γ A (.sort R.1) t v j u R.2 hget hv hvT⟩
  | _, _, _, _, _, .linst E a n Γ _ A ls hls hlen D =>
      let R := D.reg
      ⟨instLevel ls R.1, .linst E a n Γ A (.sort R.1) ls hls hlen R.2⟩
  | _, _, _, _, _, .ewk E₀ E n Γ _ A hext D =>
      let R := D.reg
      ⟨R.1, .ewk E₀ E n Γ A (.sort R.1) hext R.2⟩
  | _, _, _, _, _, .cctx E n Γ _ T A A' u D hA =>
      let R := D.reg
      ⟨R.1, .cctx E n Γ T (.sort R.1) A A' u R.2 hA⟩

/-- The position of the node `.val` literally returns — `some p` only for
    `.original`/`.admissionRead` refs, whose `.val` is the node at `p`.
    Projections return a *different* node (the projection of the node at
    `p`), views return a transported source, and `sortNode`/`indexCast`
    carry no position, so all of them report `none`: a positional receipt
    can never be inherited through a ref that does not itself read there. -/
def DRef.pos? {F : RawForest} : DRef F → Option (FieldPath F)
  | .original p | .admissionRead p => some p
  | _ => none

/-- A `TyNode`'s own transport construction, read off the node's stored
    fields — `wk`'s cutoff/declaration `d c`, `esub`'s/`lsub`'s source
    context `Γ₀`, index `j` and looked-up type `t` (and value `v`),
    `linst`'s arity and level list `ls`, `ewk`'s source environment `E₀`,
    `cctx`'s bridged source `D`. `none` for non-transport ctors. -/
inductive TyNode.TransportView (E : ResolvedEnv) (n : Nat) : Type where
  | wk (Γ₀ : LCtx) (e A : Expr Nat) (d : LocalDecl) (c : Nat)
      (D : TyNode E n Γ₀ e A)
  | esub (Γ₀ : LCtx) (e A t v : Expr Nat) (j : Nat) (D : TyNode E n Γ₀ e A)
  | lsub (Γ₀ : LCtx) (e A t v : Expr Nat) (j : Nat) (D : TyNode E n Γ₀ e A)
  | linst (a' : Nat) (Γ₀ : LCtx) (e A : Expr Nat) (ls : List Level)
      (D : TyNode E a' Γ₀ e A)
  | ewk (E₀ : ResolvedEnv) (Γ₀ : LCtx) (e A : Expr Nat) (hext : EnvExt E₀ E)
      (D : TyNode E₀ n Γ₀ e A)
  | cctx (Γ₀ : LCtx) (e T A A' : Expr Nat)
      (D : TyNode E n (.assumption A :: Γ₀) e T)

/-- Read a `TyNode`'s own transport construction; `none` for any other ctor. -/
def TyNode.transportView? : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {e T : Expr Nat} → TyNode E n Γ e T → Option (TyNode.TransportView E n)
  | _, _, _, _, _, .wk _ _ Γ₀ _ _ d c D => some (.wk Γ₀ _ _ d c D)
  | _, _, _, _, _, .esub _ _ Γ₀ _ _ t v j _ D _ _ _ => some (.esub Γ₀ _ _ t v j D)
  | _, _, _, _, _, .lsub _ _ Γ₀ _ _ t v j _ D _ _ _ => some (.lsub Γ₀ _ _ t v j D)
  | _, _, _, _, _, .linst _ a' _ Γ₀ _ _ ls _ _ D => some (.linst a' Γ₀ _ _ ls D)
  | _, _, _, _, _, .ewk E₀ _ _ Γ₀ _ _ hext D => some (.ewk E₀ Γ₀ _ _ hext D)
  | _, _, _, _, _, .cctx _ _ Γ₀ _ _ A A' _ D _ => some (.cctx Γ₀ _ _ A A' D)
  | _, _, _, _, _, _ => none

/-- A `CvNode`'s own transport construction — same scheme as `TyNode`;
    `CvNode` has no `lsub` ctor. -/
inductive CvNode.TransportView (E : ResolvedEnv) (n : Nat) : Type where
  | wk (Γ₀ : LCtx) (a b T : Expr Nat) (d : LocalDecl) (c : Nat)
      (h : CvNode E n Γ₀ a b T)
  | esub (Γ₀ : LCtx) (a b T t v : Expr Nat) (j : Nat) (h : CvNode E n Γ₀ a b T)
  | linst (a' : Nat) (Γ₀ : LCtx) (a b T : Expr Nat) (ls : List Level)
      (h : CvNode E a' Γ₀ a b T)
  | ewk (E₀ : ResolvedEnv) (Γ₀ : LCtx) (a b T : Expr Nat) (hext : EnvExt E₀ E)
      (h : CvNode E₀ n Γ₀ a b T)
  | cctx (Γ₀ : LCtx) (a b T A A' : Expr Nat)
      (h : CvNode E n (.assumption A :: Γ₀) a b T)

/-- Read a `CvNode`'s own transport construction; `none` for any other ctor. -/
def CvNode.transportView? : {E : ResolvedEnv} → {n : Nat} → {Γ : LCtx} →
    {a b T : Expr Nat} → CvNode E n Γ a b T → Option (CvNode.TransportView E n)
  | _, _, _, _, _, _, .wk _ _ Γ₀ _ _ _ d c h => some (.wk Γ₀ _ _ _ d c h)
  | _, _, _, _, _, _, .esub _ _ Γ₀ _ _ _ t v j _ h _ _ _ => some (.esub Γ₀ _ _ _ t v j h)
  | _, _, _, _, _, _, .linst _ a' _ Γ₀ _ _ _ ls _ _ h => some (.linst a' Γ₀ _ _ _ ls h)
  | _, _, _, _, _, _, .ewk E₀ _ _ Γ₀ _ _ _ hext h => some (.ewk E₀ Γ₀ _ _ _ hext h)
  | _, _, _, _, _, _, .cctx _ _ Γ₀ _ _ _ A A' _ h _ => some (.cctx Γ₀ _ _ _ A A' h)
  | _, _, _, _, _, _, _ => none

/-- Deterministic `.val`: an `original`/`admissionRead` reads the selected
    field slot of its position; `reg`/`dl`/`dr` read the node's real
    projection (`TyNode.reg`, `CvNode.dl`, `CvNode.dr`). Every view is a
    *checked read of the original site's own construction*: the resolved
    node must be that transport constructor, its stored parameters must
    equal the view's declared ones (cutoff/declaration `d c` for `wk`,
    `Γ t j`/`Γ t v j` plus the `hv`/`hvT` receipt positions for
    `esub`/`lsub`, the stored level list `ls` for `linst`, the bridge
    position for `cctx`), and the returned value is that node's own source
    field — never an arbitrary child, never a recomputed or fabricated
    field. Positional checks go through `DRef.pos?`, which reports a
    position only for refs that actually read the node there — a
    non-resolving or view-wrapped ref reports `none` and fails the check.
    `ewk`'s inclusion is bound to the transport's actual environments at
    construction: `hbound` proves the node at `pos` is an `ewk` with the
    view's declared `E₀`/`E`, and `.val` fires only when `ref` literally
    reads the node at `pos`. A reference with no such read is `none`. -/
def DRef.val {F : RawForest} : DRef F → Option RawForest
  | .original p | .admissionRead p => p.node
  | .reg p => p.node.bind fun
      | .ty t => some (.ty t.reg.2)
      | _ => none
  | .dl p => p.node.bind fun
      | .cv c => some (.ty c.dl)
      | _ => none
  | .dr p => p.node.bind fun
      | .cv c => some (.ty c.dr)
      | _ => none
  | .wkView ref d c =>
      ref.val.bind fun
        | .ty t => t.transportView?.bind fun
            | .wk _ _ _ d' c' D =>
                if d' = d ∧ c' = c then some (.ty D) else none
            | _ => none
        | .cv cn => cn.transportView?.bind fun
            | .wk _ _ _ _ d' c' h =>
                if d' = d ∧ c' = c then some (.cv h) else none
            | _ => none
        | _ => none
  | .esubView ref Γ t j _ hv hvT =>
      ref.val.bind fun
        | .ty tn => tn.transportView?.bind fun
            | .esub Γ₀ _ _ t' _ j' D =>
                match ref.pos? with
                | some p =>
                    if Γ₀ = Γ ∧ t' = t ∧ j' = j ∧
                        hv.pos? = some ⟨p.nodePath ++ [p.field], 1⟩ ∧
                        hvT.pos? = some ⟨p.nodePath ++ [p.field], 2⟩
                    then some (.ty D) else none
                | none => none
            | _ => none
        | .cv cn => cn.transportView?.bind fun
            | .esub Γ₀ _ _ _ t' _ j' h =>
                match ref.pos? with
                | some p =>
                    if Γ₀ = Γ ∧ t' = t ∧ j' = j ∧
                        hv.pos? = some ⟨p.nodePath ++ [p.field], 1⟩ ∧
                        hvT.pos? = some ⟨p.nodePath ++ [p.field], 2⟩
                    then some (.cv h) else none
                | none => none
            | _ => none
        | _ => none
  | .lsubView ref Γ t v j _ hv hvT =>
      ref.val.bind fun
        | .ty tn => tn.transportView?.bind fun
            | .lsub Γ₀ _ _ t' v' j' D =>
                match ref.pos? with
                | some p =>
                    if Γ₀ = Γ ∧ t' = t ∧ v' = v ∧ j' = j ∧
                        hv.pos? = some ⟨p.nodePath ++ [p.field], 1⟩ ∧
                        hvT.pos? = some ⟨p.nodePath ++ [p.field], 2⟩
                    then some (.ty D) else none
                | none => none
            | _ => none
        | _ => none
  | .linstView ref ls =>
      ref.val.bind fun
        | .ty t => t.transportView?.bind fun
            | .linst _ _ _ _ ls' D =>
                if ls' = ls then some (.ty D) else none
            | _ => none
        | .cv cn => cn.transportView?.bind fun
            | .linst _ _ _ _ _ ls' h =>
                if ls' = ls then some (.cv h) else none
            | _ => none
        | _ => none
  | .ewkView ref pos _ _ =>
      if ref.pos? = some pos then
        ref.val.bind fun
          | .ty t => t.transportView?.bind fun
              | .ewk _ _ _ _ _ D => some (.ty D)
              | _ => none
          | .cv cn => cn.transportView?.bind fun
              | .ewk _ _ _ _ _ _ h => some (.cv h)
              | _ => none
          | _ => none
      else none
  | .cctxView ref bridge =>
      ref.val.bind fun
        | .ty t => t.transportView?.bind fun
            | .cctx _ _ _ _ _ D =>
                match ref.pos? with
                | some p =>
                    if bridge = ⟨p.nodePath ++ [p.field], 1⟩
                    then some (.ty D) else none
                | none => none
            | _ => none
        | .cv cn => cn.transportView?.bind fun
            | .cctx _ _ _ _ _ _ h =>
                match ref.pos? with
                | some p =>
                    if bridge = ⟨p.nodePath ++ [p.field], 1⟩
                    then some (.cv h) else none
                | none => none
            | _ => none
        | _ => none
  | .sortNode .. | .indexCast _ => none

/-! ## §2 — places, sites, edges, routes -/

/-- A display place: resolved environment, level arity, working context. -/
structure Place : Type where
  env : ResolvedEnv
  arity : Nat
  ctx : LCtx

/-- The root site: the original working scope `S`, level map `σ`, and the
    forest node read at `owner`. -/
structure RootSite (F : RawForest) : Type where
  owner : FieldPath F
  node : RawForest
  hpos : owner.node = some node
  {Eₐ E : ResolvedEnv}
  {n : Nat}
  {Γ : LCtx}
  S : ScopedCtx Eₐ E n Γ
  σ : Level → Level
  place : Place
  hplace : place = { env := E, arity := n, ctx := Γ }

/-- The actual binder-parent payload: the real `pi` or `lam` constructor
    with its own domain/body fields — never an arbitrary `TyP`. `hA` and
    `hb` are the constructor's own fields, so a site can never stitch the
    domain/body of one node onto another node's typing (a `.sort` node, with
    no domain or body fields, can never be an `assumeBody` parent). -/
inductive AssumeBodyParent (E : ResolvedEnv) (n : Nat) (Γ : LCtx) : Type where
  | pi (A : Expr Nat) (u : Level) (B : Expr Nat) (v : Level)
      (hA : TyP E n Γ A (.sort u)) (hB : TyP E n (.assumption A :: Γ) B (.sort v))
  | lam (A : Expr Nat) (u : Level) (body B : Expr Nat) (v : Level)
      (hA : TyP E n Γ A (.sort u)) (hbody : TyP E n (.assumption A :: Γ) body B)
      (hB : TyP E n (.assumption A :: Γ) B (.sort v))

/-- The binder's declared domain. -/
def AssumeBodyParent.A {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Expr Nat
  | .pi A _ _ _ _ _ | .lam A _ _ _ _ _ _ _ => A

/-- The domain's sort level. -/
def AssumeBodyParent.u {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Level
  | .pi _ u _ _ _ _ | .lam _ u _ _ _ _ _ _ => u

/-- The parent's real domain-field typing. -/
def AssumeBodyParent.hA {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (p : AssumeBodyParent E n Γ) → TyP E n Γ p.A (.sort p.u)
  | .pi _ _ _ _ hA _ => hA
  | .lam _ _ _ _ _ hA _ _ => hA

/-- The body expression (`B` for `pi`, `body` for `lam`). -/
def AssumeBodyParent.b {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Expr Nat
  | .pi _ _ B _ _ _ => B
  | .lam _ _ body _ _ _ _ _ => body

/-- The body's type (`.sort v` for `pi`, `B` for `lam`). -/
def AssumeBodyParent.B {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Expr Nat
  | .pi _ _ _ v _ _ => .sort v
  | .lam _ _ _ B _ _ _ _ => B

/-- The parent's real body-field typing. -/
def AssumeBodyParent.hb {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (p : AssumeBodyParent E n Γ) → TyP E n (.assumption p.A :: Γ) p.b p.B
  | .pi _ _ _ _ _ hB => hB
  | .lam _ _ _ _ _ _ hbody _ => hbody

/-- The parent expression. -/
def AssumeBodyParent.e {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Expr Nat
  | .pi A _ B _ _ _ => .pi A B
  | .lam A _ body _ _ _ _ _ => .lam A body

/-- The parent's type. -/
def AssumeBodyParent.T {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    AssumeBodyParent E n Γ → Expr Nat
  | .pi _ u _ v _ _ => .sort (.imax u v)
  | .lam A _ _ B _ _ _ _ => .pi A B

/-- The parent typing rebuilt from the payload's own fields. -/
def AssumeBodyParent.ty {E : ResolvedEnv} {n : Nat} {Γ : LCtx} :
    (p : AssumeBodyParent E n Γ) → TyP E n Γ p.e p.T
  | .pi A u B v hA hB => .pi E n Γ A u B v hA hB
  | .lam A u body B v hA hbody hB => .lam E n Γ A u body B v hA hbody hB

/-- Binder-body edge site: the actual `lam`/`pi` constructor payload —
    `hpos` pins the owner position to the node rebuilt from exactly that
    payload. -/
structure AssumeBodySite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  payload : AssumeBodyParent E n Γ
  hpos : owner.node = some (.ty (TyP.toTyNode payload.ty))
  parent : Place
  child : Place
  hparent : parent = { env := E, arity := n, ctx := Γ }
  hchild : child = { env := E, arity := n, ctx := .assumption payload.A :: Γ }

/-- Let-body edge site: the `letE` node's complete payload. -/
structure LetBodySite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {A : Expr Nat} {u : Level}
  {value B body : Expr Nat} {w : Level}
  hA : TyP E n Γ A (.sort u)
  hv : TyP E n Γ value A
  hb : TyP E n (.letBinding A value :: Γ) body B
  hT : TyP E n Γ (instantiate0 value B) (.sort w)
  hpos : owner.node = some (.ty (TyP.toTyNode (.letE E n Γ A u value B body w
      hA hv hb hT)))
  parent : Place
  child : Place
  hparent : parent = { env := E, arity := n, ctx := Γ }
  hchild : child = { env := E, arity := n, ctx := .letBinding A value :: Γ }

/-- `wk` transport edge site: weakening at `insertAt d c`. -/
structure WkSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
  (d : LocalDecl) (c : Nat)
  D : TyP E n Γ e A
  hpos : owner.node = some (.ty (TyP.toTyNode (.wk E n Γ e A d c D)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := insertAt d c Γ }
  hsource : source = { env := E, arity := n, ctx := Γ }

/-- `esub` transport edge site: substitution of an `.assumption` entry. -/
structure EsubSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
  {u : Level}
  D : TyP E n Γ e A
  hget : Γ[j]? = some (.assumption t)
  hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)
  hpos : owner.node = some (.ty (TyP.toTyNode (.esub E n Γ e A t v j u
      D hget hv hvT)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := substRemove v j Γ }
  hsource : source = { env := E, arity := n, ctx := Γ }

/-- `lsub` transport edge site: substitution of a `.letBinding` entry. -/
structure LsubSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A t v : Expr Nat} {j : Nat}
  {u : Level}
  D : TyP E n Γ e A
  hget : Γ[j]? = some (.letBinding t v)
  hv : TyP E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t)
  hvT : TyP E n (substRemove v j Γ) (lift 0 j t) (.sort u)
  hpos : owner.node = some (.ty (TyP.toTyNode (.lsub E n Γ e A t v j u
      D hget hv hvT)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := substRemove v j Γ }
  hsource : source = { env := E, arity := n, ctx := Γ }

/-- `linst` transport edge site: level instantiation at `instLvlsCtx`. -/
structure LinstSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {a' n : Nat} {Γ : LCtx} {e A : Expr Nat}
  (ls : List Level)
  (hls : levelsBounded n ls = true) (hlen : ls.length = a')
  D : TyP E a' Γ e A
  hpos : owner.node = some (.ty (TyP.toTyNode (.linst E a' n Γ e A ls
      hls hlen D)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := instLvlsCtx ls Γ }
  hsource : source = { env := E, arity := a', ctx := Γ }

/-- `ewk` transport edge site: environment extension. -/
structure EwkSite (F : RawForest) : Type where
  owner : FieldPath F
  {E₀ E : ResolvedEnv} {n : Nat} {Γ : LCtx} {e A : Expr Nat}
  (hext : EnvExt E₀ E)
  D : TyP E₀ n Γ e A
  hpos : owner.node = some (.ty (TyP.toTyNode (.ewk E₀ E n Γ e A hext D)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := Γ }
  hsource : source = { env := E₀, arity := n, ctx := Γ }

/-- `cctx` transport edge site: context conversion of the innermost binder. -/
structure CctxSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx} {a b T A A' : Expr Nat} {u : Level}
  h : CvP E n (.assumption A :: Γ) a b T
  hA : CvP E n Γ A A' (.sort u)
  hpos : owner.node = some (.cv (CvP.toCvNode (.cctx E n Γ a b T A A' u
      h hA)))
  target : Place
  source : Place
  htarget : target = { env := E, arity := n, ctx := .assumption A' :: Γ }
  hsource : source = { env := E, arity := n, ctx := .assumption A :: Γ }

/-- The actual receipt that produced a tail cut `k` — §3's "real lookup,
    binder bridge or original receipt position". Each arm pins `k` to a
    real forest node's own construction; the `owner` position must read
    exactly that node (`hpos`):

    - `bvar`: a real `TyP.bvar` lookup of `Γ[i]`; the tail is the context
      below the looked-up slot, `k = i + 1`.
    - `assumption`/`letBinding`: a real `CtxP` binder node whose own parent
      context is `Γ.drop k`; `hdrop` forces `Γ[k-1]` to be that very binder,
      so the bridge's stored tail IS this context's own tail.
    - `ctxRoot`: the tail's own original context receipt — the `CtxP` node
      of `Γ.drop k` itself. -/
inductive TailReceipt (F : RawForest) (owner : FieldPath F) (E : ResolvedEnv)
    (n : Nat) (Γ : LCtx) (k : Nat) : Type where
  | bvar (i : Nat) (A : Expr Nat) (u : Level)
      (hlook : lookupType Γ i = some A) (hA : TyP E n Γ A (.sort u))
      (hk : k = i + 1)
      (hpos : owner.node = some (.ty (TyP.toTyNode (.bvar E n Γ i A u hlook hA))))
  | assumption (A : Expr Nat) (u : Level)
      (hdrop : Γ.drop (k - 1) = .assumption A :: Γ.drop k)
      (hΓ : CtxP E n (Γ.drop k)) (hA : TyP E n (Γ.drop k) A (.sort u))
      (hpos : owner.node = some (.ctx
        (CtxP.toCtxNode (.assumption E n (Γ.drop k) A u hΓ hA))))
  | letBinding (A v : Expr Nat) (u : Level)
      (hdrop : Γ.drop (k - 1) = .letBinding A v :: Γ.drop k)
      (hΓ : CtxP E n (Γ.drop k)) (hA : TyP E n (Γ.drop k) A (.sort u))
      (hv : TyP E n (Γ.drop k) v A)
      (hpos : owner.node = some (.ctx
        (CtxP.toCtxNode (.letBinding E n (Γ.drop k) A u v hΓ hA hv))))
  | ctxRoot (hΓ : CtxP E n (Γ.drop k))
      (hpos : owner.node = some (.ctx (CtxP.toCtxNode hΓ)))

/-- Slot-tail edge site: a real tail position `k` of the current context,
    bound by `receipt` to the actual lookup, binder bridge, or original
    context receipt that produced it — never an arbitrary `k` with an
    unrelated occupied position. -/
structure TailSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  (k : Nat) (hΓ : k ≤ Γ.length)
  receipt : TailReceipt F owner E n Γ k
  parent : Place
  child : Place
  hparent : parent = { env := E, arity := n, ctx := Γ }
  hchild : child = { env := E, arity := n, ctx := Γ.drop k }

/-- Admission edge site: a real member read `E.members r = some m` carrying
    the original call's level list `ls`. `hpos` ties the owner position to
    the original `const` call node whose own fields are exactly this
    `r`/`ls`/`m`/`hres` — the site's `ls` and member read can never come
    from anywhere but that original call. -/
structure AdmissionSite (F : RawForest) : Type where
  owner : FieldPath F
  {E : ResolvedEnv} {n : Nat} {Γ : LCtx}
  (r : Nat) (m : CheckedMember) (hres : E.members r = some m)
  (ls : List Level)
  hpos : ∃ (u : Level) (ls₀ : List Level) (hlen : ls.length = m.arity)
      (hwf : levelsBounded n ls = true) (hls : eqNList ls ls₀)
      (hT : TyP E n Γ (instantiateLevels ls₀ m.mtype) (.sort u)),
    owner.node = some (.ty (TyP.toTyNode
      (.const E n Γ r ls ls₀ m u hres hlen hwf hls hT)))
  caller : Place
  stored : Place
  hcaller : caller = { env := E, arity := n, ctx := Γ }
  hstored : stored = { env := E, arity := m.arity, ctx := [] }

/-- §2's edge grammar: one constructor per `*Site`, parent/child or
    target/source as the site records it. -/
inductive RouteEdge (F : RawForest) : Place → Place → Type where
  | assumeBody (s : AssumeBodySite F) : RouteEdge F s.parent s.child
  | letBody (s : LetBodySite F) : RouteEdge F s.parent s.child
  | wkSource (s : WkSite F) : RouteEdge F s.target s.source
  | esubSource (s : EsubSite F) : RouteEdge F s.target s.source
  | lsubSource (s : LsubSite F) : RouteEdge F s.target s.source
  | linstSource (s : LinstSite F) : RouteEdge F s.target s.source
  | ewkSource (s : EwkSite F) : RouteEdge F s.target s.source
  | cctxSource (s : CctxSite F) : RouteEdge F s.target s.source
  | tail (s : TailSite F) : RouteEdge F s.parent s.child
  | admission (s : AdmissionSite F) : RouteEdge F s.caller s.stored

/-- A display route: root site plus a spine of edges. No `.same` constructor;
    sibling/reg/dl-dr requests reuse the same route. -/
inductive DisplayRoute (F : RawForest) : Place → Type where
  | root (s : RootSite F) : DisplayRoute F s.place
  | step {p q : Place} : DisplayRoute F p → RouteEdge F p q → DisplayRoute F q

/-! ## §3 — the computed route state, one equation per edge -/

/-- The state `eval` computes: environment, arity, working context, level map
    `σ`, display `ρ`. -/
structure RouteState : Type where
  env : ResolvedEnv
  arity : Nat
  ctx : LCtx
  map : Level → Level
  disp : List Disp

/-- One clause of §3's table per edge constructor. `rV = hv.eps σ ρ` and
    `κ(j) = countKeep (ρ.take j)` are computed inside the clauses that need
    them; `lsubSource` inserts `inline (localize κ rV)`; `cctxSource` keeps
    the same `ρ`. -/
noncomputable def edgeStep {F : RawForest} {p q : Place} (st : RouteState) :
    RouteEdge F p q → RouteState
  | .assumeBody s =>
      { st with ctx := .assumption s.payload.A :: st.ctx,
                disp := binderDisp (levelIsZero (st.map s.payload.u)) :: st.disp }
  | .letBody s =>
      let rV := s.hv.eps st.map st.disp
      { st with ctx := .letBinding s.A s.value :: st.ctx,
                disp := (if rV = .star then .drop else .inline rV) :: st.disp }
  | .wkSource s => { st with ctx := s.Γ, disp := removeAt st.disp s.c }
  | .esubSource s =>
      { st with ctx := s.Γ,
                disp := insertDisp (binderDisp (levelIsZero (st.map s.u))) s.j st.disp }
  | .lsubSource s =>
      let rV := s.hv.eps st.map st.disp
      let κ := countKeep (st.disp.take s.j)
      { st with ctx := s.Γ,
                disp := insertDisp (if rV = .star then .drop
                      else .inline (localize κ rV)) s.j st.disp }
  | .linstSource s =>
      { env := st.env, arity := s.a', ctx := s.Γ,
        map := fun l => st.map (instLevel s.ls l), disp := st.disp }
  | .ewkSource s => { st with env := s.E₀ }
  | .cctxSource s => { st with ctx := .assumption s.A :: s.Γ }
  | .tail s => { st with ctx := s.Γ.drop s.k, disp := st.disp.drop s.k }
  | .admission s =>
      { env := st.env, arity := s.m.arity, ctx := [],
        map := fun l => st.map (instLevel s.ls l), disp := [] }

/-- §3's table, literally. `eval` is structural recursion on the route: it
    calls no P2, `hcoh`, `CL` or `PBit`. -/
noncomputable def eval {F : RawForest} {p : Place} : DisplayRoute F p → RouteState
  | .root s => { env := s.place.env, arity := s.place.arity, ctx := s.place.ctx,
                 map := s.σ, disp := s.S.can s.σ }
  | .step r e => edgeStep (eval r) e

/-! ## §1–§2 controls -/

/-- Two `FieldPath`s that differ only in `field` are different positions even
    when they read the same node — `refl`'s `h`/`dl`/`dr` stay three distinct
    positions. -/
theorem fieldPath_distinct_field {F : RawForest} (np : List Nat) {i j : Nat}
    (h : i ≠ j) : (⟨np, i⟩ : FieldPath F) ≠ ⟨np, j⟩ := by
  intro he; exact h (FieldPath.mk.inj he).2

/-- The node at an `EsubSite`'s owner is exactly the node rebuilt from the
    site's own `D`/`hget`/`hv`/`hvT`: a site stitched from two different
    `esub` nodes can never satisfy `hpos`, so it is unconstructible. -/
theorem esubSite_node_forced {F : RawForest} (s : EsubSite F) (n : RawForest)
    (hn : s.owner.node = some n) :
    n = .ty (TyP.toTyNode (.esub _ _ _ _ _ _ _ _ _ s.D s.hget s.hv s.hvT)) := by
  rw [s.hpos] at hn; exact (Option.some.inj hn).symm

/-! ## positive control — a conversion `ewk` resolves through `ewkView` -/

/- The audit's Q254 input: `CvNode.ewk` over `CvNode.refl`, selected under
   `CvNode.symm`'s own `h` slot `⟨[], 0⟩`. The conversion arm of `hbound`
   pins the node's stored env args to the declared `E₀`/`E`, and `.val`
   resolves to the `refl` source. -/
namespace EwkCvControl

/-- `E₀` is empty; `E` adds an axiom member — the supplied inclusion is a
    real `EnvExt` (vacuous on the empty source). -/
def E₀ : ResolvedEnv := emptyEnv
def E : ResolvedEnv := extendEnv emptyEnv 0 ⟨.axiomM, 0, .sort .zero, none⟩
def hext : EnvExt E₀ E := fun _ _ h => Option.noConfusion h

/-- `.sort .zero : .sort (.succ .zero)`, in each env. -/
def tyE : TyNode E 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort E 0 _ .zero (.succ .zero) (fun _ => rfl)
def tyE₀ : TyNode E₀ 0 [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort E₀ 0 _ .zero (.succ .zero) (fun _ => rfl)

/-- `CvNode.refl` over that typing, in the source env. -/
def refl : CvNode E₀ 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .refl E₀ 0 _ _ _ tyE₀ tyE₀ tyE₀

/-- The conversion `ewk` transport of `refl` along `hext`. -/
def ewkN : CvNode E 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .ewk E₀ E 0 _ _ _ _ hext refl

/-- `symm` over it — its `h` slot (child `0`) is the `ewk` node. -/
def symmN : CvNode E 0 [] (.sort .zero) (.sort .zero) (.sort (.succ .zero)) :=
  .symm E 0 _ _ _ _ ewkN tyE tyE

/-- The control forest: the `symm` node at root. -/
def F : RawForest := .cv symmN

/-- The `ewk` child's position. -/
def pos : FieldPath F := ⟨[], 0⟩

/-- The conversion arm of `hbound`: `pos` reads a `CvNode.ewk` whose stored
    env args are exactly the declared `E₀`/`E`. -/
def bound : ∃ (n : Nat) (Γ : LCtx) (a b T : Expr Nat)
    (hext' : EnvExt E₀ E) (h : CvNode E₀ n Γ a b T),
    pos.node = some (.cv (.ewk E₀ E n Γ a b T hext' h)) :=
  ⟨0, [], _, _, _, hext, refl, rfl⟩

/-- The view: an `ewkView` over the direct read of `pos`, endpoints bound. -/
def view : DRef F := .ewkView (.original pos) pos hext (.inr bound)

/-- Positive control: the conversion `ewk` view resolves to the node's own
    source field — the `refl` conversion — so the mandatory `hbound` keeps
    the conversion case working. -/
theorem resolves : view.val = some (.cv refl) := rfl

end EwkCvControl

end Rcic.Syn
