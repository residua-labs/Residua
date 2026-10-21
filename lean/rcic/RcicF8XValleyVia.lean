import rcic.RcicF8XValleyStrict
import rcic.RcicF8CtxWfVia
import rcic.RcicF8CtxWfViaS

/-!
# `RcicF8XValleyVia` — the strict valley route with the weakening pushed to the literals (WK-1b)

WK-1b of W-X-WK (#7128 ruling Q3/Q4). The strict route of #7142
(`RcicF8XValleyStrict`) with the weakening carried as a PENDING context
morphism `ρ : Wk Γ₀ Γ'` from the current node's context down to the
literals: every `wk` step (at every cutoff, `bCvW`/`bLinkW` flip the
landed `match k` refusal into descent) accumulates into `ρ`, and every
result is returned AT the segment context `Γ'`. U, D and S therefore run
at `Γ'` with the caller's `hΓ'`, through the per-segment view
`SuppliersVia.atSeg`; the only call under the weakening is J, which
receives the WK-1a premise `⟨Γ', ρ, hΓ'⟩ : CtxWfVia Γ₀`.

S at the segment context is BY CONSTRUCTION on the J path (audit P2 of
#7162): J answers at `Γ₀`, and `SOut.thin` would wrap its stars in lazy
`EvParStar.wk`, which the inherited `readStarC` unwraps — calling `X.S`
on source-context steps. The route instead returns J's valley through
`Valley.thinDeep` (§1b), which pushes `ρ` into each step's payload, so
every step the inherited readers meet is already at `Γ'` and S is invoked
there. `subst0`/`substLet` are not commuted: `Wk` cannot queue a
substitution, so `thinWk` still reifies `ρ` as `EvParStar.wk` around the
subst node (the `j < c` wall `valS` also refuses). That reification does
not preserve the segment context — the inherited reader unwraps it and
calls `X.S` on the source star — so the lit accept arm refuses any
returned star that still contains those constructors (`Valley.admitSubst`)
before `readStarC` runs. Segment-level re-entry of substitution is
W-X-SUBST slice 2 (#7207), not built here.
Lazy `wk` wrappers can still occur INSIDE a supplier's own answer
(a supplier's returned star may carry `EvParStar.wk` nodes); those are
read exactly as #7142 reads them — the inherited reader descends the
wrapper and calls S at the inner context, which is that supplier's own
decomposition, not this route's transport. The lazy `Valley.thin`/
`SRes.thin`/`SOut.thin` stay for the `.refl D` arm, whose output carries
no steps.

The census shape, `SOut.Bound`, `SegOut`, `census`, `EdgeContractLex` and
the measure are those of #7142, unchanged — `xValleySVia_edges` is
literally `census_edges`. The two recursive descents
(`svalleyCv`→`svalleyCvVia`, `slinkValley`→`slinkValleyVia`) and the thin
dispatchers that call them (`sprefixValley`/`xSegS`/`xSegsS`/`xValleyS?`
→ `…Via`) are re-stated here; `scombine`, `sjoin`, `sread`,
`SegOut.comp`, `xStructTc`, `readStarC`/`readValleyC` are reused through
`atSeg`.

Q4: D takes the context-conditioned partial shape `DProcWfP` — it is
handed the `CtxWfT Γ` of the context it answers at, so D1's `dProcWf` is
a supplier (`d1WfP`), the premise is forwarded never invented
(`DProcWfP.ofTotal_eq`), and `atSeg`'s D answers only where the `CtxWfT`
is real (`SuppliersVia.atSeg_D_ne`).

Amendment (Q-S1-1 of #7207, reworked after #7202 and #7277 landed):
the worker's premise is WK-2's `CtxWfViaS` — the route is re-enterable
at ANY context, including the source context of a substitution (slice
2, W-X-SUBST). The worker takes the premise-free `Suppliers` bundle AT
the call context (one invocation has one fixed context, so the
context-conditioning was constant anyway) plus WK-2's `JProcViaSP`
front and its contract; the landed names are the `ofWf` instances —
`X.atSeg hΓ` as the `Suppliers`, `JProcViaP.toViaSP X.J` as the J
front — with `*_eq` agreement by `rfl`. The D-side ViaS interface is
D-owned and landed (`RcicF8DViaSSupply`, #7277 — which imports THIS
module for `DProcWfP`/`d1WfP`), so the `SuppliersViaS` bundle layer
sits above it in `RcicF8XValleyViaS`; what stays here is the J lift —
`JProcViaP.toViaSP` answers `ins`-only witnesses recovered by
`CtxMorph.toWk?`, faithful on every witness the `ofWf` route builds
(`JProcViaP.toViaSP_viaS`) and honest elsewhere — a substituted witness
is refused (`JProcViaP.toViaSP_sub_none`).

Teeth: a weakening never maps a context onto its own tail
(`no_wk_to_tail`), so the inner context of an `esub 0` link has no WK-1
Via witness from the outer context's well-formedness
(`no_via_across_esub0`) — the worker's `esub` refusal (`bCvW_esub`) is
forced, not chosen; WK-2's typed `sub` arm is what admits it. The
premise-forgetting `CtxWfViaMut` crosses it untyped
(`mutant_crosses_esub0`), and `hΓ` cannot be invented
(`invent_hΓ_impossible`). `closure_claim = 0`.
-/

namespace Rcic.Declarative.F8Measure

open Rcic.Syn

variable {E : ResolvedEnv} {n : Nat} {R : List (Jd E n)} {Γ : LCtx}

/-! ### §1 thinning kit — folds of the landed `.wk` over `Wk`

`(Wk.ins d k ρ).map e = ρ.map (lift k 1 e)` holds by `rfl`, so each `thin`
is structural recursion on `ρ`, one landed `.wk` per insertion. -/

/-- a provenance typing moves along the pending weakening. -/
def EvTy.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {e T : Expr Nat} →
    EvTy R Γ₀ e T → EvTy R Γ' (ρ.map e) (ρ.map T)
  | _, _, .id _, _, _, h => h
  | _, _, .ins d k ρ, _, _, h => EvTy.thin ρ (EvTy.wk d k h)

/-- a provenance chain moves along the pending weakening. -/
def EvTc.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {A B : Expr Nat} →
    EvTc R Γ₀ A B → EvTc R Γ' (ρ.map A) (ρ.map B)
  | _, _, .id _, _, _, h => h
  | _, _, .ins d k ρ, _, _, h => EvTc.thin ρ (EvTc.wk d k h)

/-- a provenance conversion moves along the pending weakening. -/
def EvCv.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    EvCv R Γ₀ a b T → EvCv R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, h => h
  | _, _, .ins d k ρ, _, _, _, h => EvCv.thin ρ (EvCv.wk d k h)

/-- a valley moves along the pending weakening. -/
def Valley.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    Valley R Γ₀ a b T → Valley R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, V => V
  | _, _, .ins d k ρ, _, _, _, V => Valley.thin ρ (Valley.wk d k V)

/-- a strict result moves along the pending weakening. -/
def SRes.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    SRes R Γ₀ a b T → SRes R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, r => r
  | _, _, .ins d k ρ, _, _, _, r => SRes.thin ρ (r.wk d k)

/-- a bounded strict output moves along the pending weakening. -/
def SOut.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    SOut R Γ₀ a b T → SOut R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, o => o
  | _, _, .ins d k ρ, _, _, _, o => SOut.thin ρ (o.wk d k)

theorem EvTy.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {e T : Expr Nat} → (D : EvTy R Γ₀ e T) → (D.thin ρ).leaves = D.leaves
  | _, _, .id _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, D => EvTy.thin_leaves ρ (EvTy.wk d k D)

theorem EvTc.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {A B : Expr Nat} → (c : EvTc R Γ₀ A B) → (c.thin ρ).leaves = c.leaves
  | _, _, .id _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, c => EvTc.thin_leaves ρ (EvTc.wk d k c)

theorem EvCv.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (c : EvCv R Γ₀ a b T) →
    (c.thin ρ).leaves = c.leaves
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, c => EvCv.thin_leaves ρ (EvCv.wk d k c)

theorem Valley.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (V : Valley R Γ₀ a b T) →
    (V.thin ρ).leaves = V.leaves
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, V => by
      simp only [Valley.thin, Valley.wk_leaves]
      exact Valley.thin_leaves ρ (Valley.wk d k V)

theorem SRes.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (r : SRes R Γ₀ a b T) →
    (r.thin ρ).leaves = r.leaves
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, r => by
      have := SRes.thin_leaves ρ (r.wk d k)
      rwa [SRes.wk_leaves] at this

theorem SRes.thin_pendingLeaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (r : SRes R Γ₀ a b T) →
    (r.thin ρ).pendingLeaves = r.pendingLeaves
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, r => by
      have := SRes.thin_pendingLeaves ρ (r.wk d k)
      rwa [SRes.wk_pendingLeaves] at this

theorem SRes.thin_isVal : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (r : SRes R Γ₀ a b T) →
    (r.thin ρ).isVal = r.isVal
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, r => by
      have := SRes.thin_isVal ρ (r.wk d k)
      rwa [SRes.isVal_wk] at this

/-- thinning preserves the strict bound: one `bound_wk` per insertion. -/
theorem SOut.bound_thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → {o : SOut R Γ₀ a b T} → {L : List (Jd E n)} →
    o.Bound L → (o.thin ρ).Bound L
  | _, _, .id _, _, _, _, _, _, h => h
  | _, _, .ins d k ρ, _, _, _, _, _, h =>
      SOut.bound_thin ρ (SOut.bound_wk d k h)

/-! ### §1b deep thinning — the weakening pushed INTO the steps

`SOut.thin` wraps a returned whole star in the LAZY `EvParStar.wk`
constructor; the inherited `readStarC` then unwraps it and recurses into
the inner star, so `X.S` is invoked on steps at the SOURCE context.
`thinDeep` is the alternative transport: the pending `ρ` is pushed into
every step's payload fields (`…Payload.wk` per producer, folded by
`EvPar.thin`/`EvParStar.thinDeep`), so every step a reader meets is
already AT `Γ'` — `X.S` runs at the segment context by construction, with
no new reader. A lazy `wk` wrapper already inside a star folds into `ρ`.
Leaves and bounds are preserved exactly (`*_wk_leaves`,
`thinDeep_leaves`). -/

/-- index cast for provenance steps (the `.lit` arm's closed expansion). -/
def EvPar.cast {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat} (hΓ : Γ = Γ')
    (ha : a = a') (hb : b = b') (hT : T = T') (h : EvPar R Γ a b T) :
    EvPar R Γ' a' b' T' := by
  subst hΓ; subst ha; subst hb; subst hT; exact h

theorem EvPar.cast_leaves {Γ Γ' : LCtx} {a a' b b' T T' : Expr Nat}
    (hΓ : Γ = Γ') (ha : a = a') (hb : b = b') (hT : T = T')
    (h : EvPar R Γ a b T) : (h.cast hΓ ha hb hT).leaves = h.leaves := by
  subst hΓ; subst ha; subst hb; subst hT; rfl

/-- a proof-index payload under one insertion, field-wise. -/
def ProofIndexPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {a b T : Expr Nat}
    (p : ProofIndexPayload R Γ a b T) :
    ProofIndexPayload R (insertAt d k Γ) (lift k 1 a) (lift k 1 b)
      (lift k 1 T) where
  proposition := lift k 1 p.proposition
  propTy := .wk d k p.propTy
  chain := .wk d k p.chain
  leftTy := .wk d k p.leftTy
  rightTy := .wk d k p.rightTy

/-- a structural-Π payload under one insertion, field-wise; the codomain
    fields sit under `.assumption A`, so their cutoff is `k + 1`
    (`insertAt d (k+1) (.assumption A :: Γ) = .assumption (lift k 1 A) ::
    insertAt d k Γ` and `lift k 1 (.pi A' B')` both reduce by `rfl`). -/
def StructPiPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T) :
    StructPiPayload R (insertAt d k Γ) (lift k 1 A) (lift (k + 1) 1 B)
      (lift k 1 A') (lift (k + 1) 1 B') (lift k 1 T) where
  u := p.u
  v := p.v
  hA := .wk d k p.hA
  hc := .wk d k p.hc
  hB := .wk d (k + 1) p.hB
  hcB := .wk d (k + 1) p.hcB
  hrt := .wk d k p.hrt
  idx := .wk d k p.idx

/-- a sort-equality payload under one insertion, field-wise (sorts lift
    to themselves, `rfl`). -/
def SortEqPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {l₁ l₂ : Level}
    {T : Expr Nat} (p : SortEqPayload R Γ l₁ l₂ T) :
    SortEqPayload R (insertAt d k Γ) l₁ l₂ (lift k 1 T) where
  T₀ := lift k 1 p.T₀
  h := p.h
  hl := .wk d k p.hl
  hr := .wk d k p.hr
  idx := .wk d k p.idx

/-- a consts payload under one insertion, field-wise (constants lift to
    themselves, `rfl`). -/
def ConstsPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {r : Nat}
    {ls ls' : List Level} {T : Expr Nat} (p : ConstsPayload R Γ r ls ls' T) :
    ConstsPayload R (insertAt d k Γ) r ls ls' (lift k 1 T) where
  T₀ := lift k 1 p.T₀
  h := p.h
  hl := .wk d k p.hl
  hr := .wk d k p.hr
  idx := .wk d k p.idx

/-- a literal payload under one insertion, field-wise; `natExpand t` is
    closed (`natExpand_lift`), so the expansion typing is cast back
    through it. -/
def LitPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {t : Nat}
    {T : Expr Nat} (p : LitPayload R Γ t T) :
    LitPayload R (insertAt d k Γ) t (lift k 1 T) where
  T₀ := lift k 1 p.T₀
  hexp := EvTy.cast rfl (natExpand_lift k 1 t) rfl (.wk d k p.hexp)
  idx := .wk d k p.idx

theorem ProofIndexPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {a b T : Expr Nat} (p : ProofIndexPayload R Γ a b T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [ProofIndexPayload.wk, ProofIndexPayload.leaves, EvTy.leaves,
    EvTc.leaves]

theorem StructPiPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {A B A' B' T : Expr Nat} (p : StructPiPayload R Γ A B A' B' T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [StructPiPayload.wk, StructPiPayload.leaves, EvTy.leaves,
    EvCv.leaves, EvTc.leaves]

theorem SortEqPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {l₁ l₂ : Level} {T : Expr Nat} (p : SortEqPayload R Γ l₁ l₂ T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [SortEqPayload.wk, SortEqPayload.leaves, EvTy.leaves,
    EvTc.leaves]

theorem ConstsPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {r : Nat} {ls ls' : List Level} {T : Expr Nat}
    (p : ConstsPayload R Γ r ls ls' T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [ConstsPayload.wk, ConstsPayload.leaves, EvTy.leaves,
    EvTc.leaves]

theorem LitPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx} {t : Nat}
    {T : Expr Nat} (p : LitPayload R Γ t T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [LitPayload.wk, LitPayload.leaves, EvTy.cast_leaves,
    EvTy.leaves, EvTc.leaves]

/-- `EvPar.refl` under one insertion, field-wise, same as the other payloads. -/
def ReflPayload.wk (d : LocalDecl) (k : Nat) {Γ : LCtx} {a T : Expr Nat}
    (p : ReflPayload R Γ a T) :
    ReflPayload R (insertAt d k Γ) (lift k 1 a) (lift k 1 T) where
  T₀ := lift k 1 p.T₀
  h := .wk d k p.h
  idx := .wk d k p.idx

theorem ReflPayload.wk_leaves (d : LocalDecl) (k : Nat) {Γ : LCtx}
    {a T : Expr Nat} (p : ReflPayload R Γ a T) :
    (p.wk d k).leaves = p.leaves := by
  simp only [ReflPayload.wk, ReflPayload.leaves, EvTy.leaves, EvTc.leaves]

/-- a provenance step under one insertion, pushed into the payload — no
    lazy `wk` wrapper exists for `EvPar`, so each producer's fields are
    weakened in place and the reader meets the producer AT the weakened
    context. -/
def EvPar.wk (d : LocalDecl) (k : Nat) : {Γ : LCtx} → {a b T : Expr Nat} →
    EvPar R Γ a b T →
    EvPar R (insertAt d k Γ) (lift k 1 a) (lift k 1 b) (lift k 1 T)
  | _, _, _, _, .proofIndex p => .proofIndex (p.wk d k)
  | _, _, _, _, .structPi p => .structPi (p.wk d k)
  | _, _, _, _, .sortEq p => .sortEq (p.wk d k)
  | _, _, _, _, .consts p => .consts (p.wk d k)
  | _, _, _, _, .lit p =>
      EvPar.cast rfl rfl (natExpand_lift k 1 _).symm rfl
        (.lit (p.wk d k))
  | _, _, _, _, .refl p => .refl (p.wk d k)

theorem EvPar.wk_leaves (d : LocalDecl) (k : Nat) : {Γ : LCtx} →
    {a b T : Expr Nat} → (h : EvPar R Γ a b T) →
    (h.wk d k).leaves = h.leaves := by
  intro Γ a b T h
  cases h with
  | proofIndex p =>
      simp only [EvPar.wk, EvPar.leaves, ProofIndexPayload.wk_leaves]
  | structPi p =>
      simp only [EvPar.wk, EvPar.leaves, StructPiPayload.wk_leaves]
  | sortEq p =>
      simp only [EvPar.wk, EvPar.leaves, SortEqPayload.wk_leaves]
  | consts p =>
      simp only [EvPar.wk, EvPar.leaves, ConstsPayload.wk_leaves]
  | lit p =>
      simp only [EvPar.wk]
      rw [EvPar.cast_leaves]
      simp only [EvPar.leaves, LitPayload.wk_leaves]
  | refl p =>
      simp only [EvPar.wk, EvPar.leaves, ReflPayload.wk_leaves]

/-- a provenance step moves along the pending weakening, pushed into the
    payload — the result's steps are at `Γ'`, unwrapped. -/
def EvPar.thin : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    EvPar R Γ₀ a b T → EvPar R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, .id _, _, _, _, h => h
  | _, _, .ins d k ρ, _, _, _, h => EvPar.thin ρ (EvPar.wk d k h)

theorem EvPar.thin_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (h : EvPar R Γ₀ a b T) →
    (h.thin ρ).leaves = h.leaves
  | _, _, .id _, _, _, _, _ => rfl
  | _, _, .ins d k ρ, _, _, _, h => by
      have e := EvPar.thin_leaves ρ (EvPar.wk d k h)
      rwa [EvPar.wk_leaves] at e

/-- Reify a pending weakening as `EvParStar.wk` nodes. `subst0`/`substLet`
    use this: `Wk` has no substitution constructor, so the substitution is
    not commuted through `ρ` (same queue policy as `EvParStar.valS`). -/
def EvParStar.thinWk : {Γ₀ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Γ₀ a b T → {Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    EvParStar R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, _, _, hs, _, .id _ => hs
  | _, _, _, _, hs, _, .ins d k ρ =>
      EvParStar.thinWk (EvParStar.wk d k hs) ρ

theorem EvParStar.thinWk_leaves : {Γ₀ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ₀ a b T) → {Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    (hs.thinWk ρ).leaves = hs.leaves
  | _, _, _, _, _, _, .id _ => rfl
  | _, _, _, _, hs, _, .ins d k ρ => by
      rw [EvParStar.thinWk]
      have hleaves := EvParStar.thinWk_leaves (EvParStar.wk d k hs) ρ
      simpa only [EvParStar.leaves] using hleaves

/-- DEEP thinning of a star: `ρ` is pushed into every step's payload, so
    a reader meets each step at `Γ'`; a lazy `wk` wrapper already inside
    the star folds into `ρ` instead. A `subst0`/`substLet` node is not
    commuted; `thinWk` reifies `ρ` around it. -/
def EvParStar.thinDeep : {Γ₀ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Γ₀ a b T → {Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    EvParStar R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, _, _, .refl h => fun ρ => EvParStar.refl (h.thin ρ)
  | _, _, _, _, .tail h hs => fun ρ =>
      EvParStar.tail (h.thin ρ) (hs.thinDeep ρ)
  | _, _, _, _, .conv hs c => fun ρ =>
      EvParStar.conv (hs.thinDeep ρ) (c.thin ρ)
  | _, _, _, _, .wk d k hs =>
      fun ρ => hs.thinDeep (.ins d k ρ)
  | _, _, _, _, .trans h₁ h₂ =>
      fun ρ => EvParStar.trans (h₁.thinDeep ρ) (h₂.thinDeep ρ)
  | _, _, _, _, .subst0 j hs hget hv =>
      fun ρ => EvParStar.thinWk (.subst0 j hs hget hv) ρ
  | _, _, _, _, .substLet j hs hget hv =>
      fun ρ => EvParStar.thinWk (.substLet j hs hget hv) ρ

theorem EvParStar.thinDeep_leaves : {Γ₀ : LCtx} → {a b T : Expr Nat} →
    (hs : EvParStar R Γ₀ a b T) → {Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    (hs.thinDeep ρ).leaves = hs.leaves
  | _, _, _, _, .refl h => fun ρ => by
      simp only [EvParStar.thinDeep, EvParStar.leaves, EvTy.thin_leaves]
  | _, _, _, _, .tail h hs => fun ρ => by
      simp only [EvParStar.thinDeep, EvParStar.leaves, EvPar.thin_leaves]
      rw [hs.thinDeep_leaves ρ]
  | _, _, _, _, .conv hs c => fun ρ => by
      simp only [EvParStar.thinDeep, EvParStar.leaves, EvTc.thin_leaves]
      rw [hs.thinDeep_leaves ρ]
  | _, _, _, _, .wk d k hs => fun ρ => by
      simp only [EvParStar.thinDeep, EvParStar.leaves]
      exact hs.thinDeep_leaves (.ins d k ρ)
  | _, _, _, _, .trans h₁ h₂ => fun ρ => by
      simp only [EvParStar.thinDeep, EvParStar.leaves]
      rw [h₁.thinDeep_leaves ρ, h₂.thinDeep_leaves ρ]
  | _, _, _, _, .subst0 j hs hget hv => fun ρ => by
      rw [EvParStar.thinDeep]
      exact EvParStar.thinWk_leaves (.subst0 j hs hget hv) ρ
  | _, _, _, _, .substLet j hs hget hv => fun ρ => by
      rw [EvParStar.thinDeep]
      exact EvParStar.thinWk_leaves (.substLet j hs hget hv) ρ

/-- DEEP thinning of a valley: both legs' steps land at `Γ'`. -/
def Valley.thinDeep : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') → {a b T : Expr Nat} →
    Valley R Γ₀ a b T → Valley R Γ' (ρ.map a) (ρ.map b) (ρ.map T)
  | _, _, ρ, _, _, _, V =>
      ⟨ρ.map V.N, V.left.thinDeep ρ, V.right.thinDeep ρ,
        V.ty₁.thin ρ, V.ty₂.thin ρ⟩

theorem Valley.thinDeep_leaves : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    {a b T : Expr Nat} → (V : Valley R Γ₀ a b T) →
    (V.thinDeep ρ).leaves = V.leaves := by
  intro Γ₀ Γ' ρ a b T V
  simp only [Valley.thinDeep, Valley.leaves, EvParStar.thinDeep_leaves,
    EvTy.thin_leaves]

/-- a star still carries a lazy substitution (`subst0` or `substLet`),
    including under `wk` / `trans` / `conv` / `tail`. -/
def EvParStar.hasSubst : {Γ : LCtx} → {a b T : Expr Nat} →
    EvParStar R Γ a b T → Bool
  | _, _, _, _, .refl _ => false
  | _, _, _, _, .tail _ hs => hs.hasSubst
  | _, _, _, _, .conv hs _ => hs.hasSubst
  | _, _, _, _, .wk _ _ hs => hs.hasSubst
  | _, _, _, _, .trans h₁ h₂ => h₁.hasSubst || h₂.hasSubst
  | _, _, _, _, .subst0 _ _ _ _ => true
  | _, _, _, _, .substLet _ _ _ _ => true

/-- either leg of a returned valley still carries a lazy substitution. -/
def Valley.hasSubst {Γ : LCtx} {a b T : Expr Nat} (V : Valley R Γ a b T) :
    Bool :=
  V.left.hasSubst || V.right.hasSubst

/-- Q92 gate. `refuse = true` drops a valley whose stars still contain
    `subst0`/`substLet`; `refuse = false` is that gate with only the
    refusal deleted (the mutant). -/
def Valley.admitSubst (refuse : Bool) {Γ : LCtx} {a b T : Expr Nat}
    (V : Valley R Γ a b T) : Option (Valley R Γ a b T) :=
  if refuse && V.hasSubst then none else some V

/-! ### §2 the W-X-WK admissible fragment

Siblings of the landed Bools; the ONLY change is `.wk` at every cutoff —
the weakening now rides in the pending morphism instead of refusing. -/

/-- a lazy conversion the Via route reads in the target of a weakening:
    exactly `bCv`'s arms, except `.wk` descends at EVERY cutoff.
    `esub`/`subst0`/`substLet`/`sorts`/`consts` stay refused. -/
def bCvW : {Γ : LCtx} → {a b T : Expr Nat} → EvCv R Γ a b T → Bool
  | _, _, _, _, .lit _ _ => true
  | _, _, _, _, .refl _ => true
  | _, _, _, _, .symm c => bCvW c
  | _, _, _, _, .trans c₁ c₂ => bCvW c₁ && bCvW c₂
  | _, _, _, _, .tyConv _ c _ => bCvW c
  | _, _, _, _, .rety c _ => bCvW c
  | _, _, _, _, .wk _ _ c => bCvW c
  | _, _, _, _, .esub .. => false
  | _, _, _, _, .subst0 .. => false
  | _, _, _, _, .substLet .. => false
  | _, _, _, _, .sorts .. => false
  | _, _, _, _, .consts .. => false

/-- a link the Via route accepts: `bLink`'s arms with `bCvW`/`bLinkW`. -/
def bLinkW : {Γ : LCtx} → {A B : Expr Nat} → EvTc R Γ A B → Bool
  | _, _, _, .ofCv _ c => bCvW c
  | _, _, _, .wk _ _ l => bLinkW l
  | _, _, _, .piCod .. => false
  | _, _, _, .subst0 .. => false
  | _, _, _, .substLet .. => false
  | _, _, _, .lit .. => false
  | _, _, _, .refl .. => false
  | _, _, _, .symm .. => false
  | _, _, _, .trans .. => false

/-- every link is a `bLinkW`. -/
def Flat.bPrefixW : {A B : Expr Nat} → Flat R Γ A B → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ rest => bLinkW l && rest.bPrefixW

/-- a segment is W-admissible when it is one Π-spined link (Stratum A) or
    one W-valley link, or a longer `bPrefixW`. -/
def Flat.segAdmW : {P M : Expr Nat} → Flat R Γ P M → Bool
  | _, _, .nil _ => true
  | _, _, .cons l _ (.nil _) => piSpinedTc l || bLinkW l
  | _, _, .cons l _ (.cons l' hl' rest') =>
      bLinkW l && (Flat.cons l' hl' rest').bPrefixW

/-- every segment is W-admissible. -/
def Segs.admW : {P Q : Expr Nat} → Segs R Γ P Q → Bool
  | _, _, .nil _ => true
  | _, _, .cons p _ rest => p.segAdmW && rest.admW

/-- admissibility of an X input under the W fragment. -/
def xAdmW {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    Bool :=
  ((flattenTc c).segment rfl).admW

/-! the fragment only grows: the landed admissible fragment is inside
    the W fragment (monotonicity). -/

theorem bCvW_of_bCv : {Γ : LCtx} → {a b T : Expr Nat} →
    (c : EvCv R Γ a b T) → bCv c = true → bCvW c = true
  | _, _, _, _, .lit _ _, _ => rfl
  | _, _, _, _, .refl _, _ => rfl
  | _, _, _, _, .symm c, h =>
      bCvW_of_bCv c (by simpa only [bCv] using h)
  | _, _, _, _, .trans c₁ c₂, h => by
      have h' := h
      simp only [bCv, Bool.and_eq_true] at h'
      simp only [bCvW, Bool.and_eq_true]
      exact ⟨bCvW_of_bCv c₁ h'.1, bCvW_of_bCv c₂ h'.2⟩
  | _, _, _, _, .tyConv _ c _, h =>
      bCvW_of_bCv c (by simpa only [bCv] using h)
  | _, _, _, _, .rety c _, h =>
      bCvW_of_bCv c (by simpa only [bCv] using h)
  | _, _, _, _, .wk _ k c, h => by
      cases k with
      | zero => exact bCvW_of_bCv c (by simpa only [bCv] using h)
      | succ k => exact nomatch h
  | _, _, _, _, .esub .., h => nomatch h
  | _, _, _, _, .subst0 .., h => nomatch h
  | _, _, _, _, .substLet .., h => nomatch h
  | _, _, _, _, .sorts .., h => nomatch h
  | _, _, _, _, .consts .., h => nomatch h

theorem bLinkW_of_bLink : {Γ : LCtx} → {A B : Expr Nat} →
    (l : EvTc R Γ A B) → bLink l = true → bLinkW l = true
  | _, _, _, .ofCv _ c, h => bCvW_of_bCv c (by simpa only [bLink] using h)
  | _, _, _, .wk _ k l, h => by
      cases k with
      | zero => exact bLinkW_of_bLink l (by simpa only [bLink] using h)
      | succ k => exact nomatch h
  | _, _, _, .piCod .., h => nomatch h
  | _, _, _, .subst0 .., h => nomatch h
  | _, _, _, .substLet .., h => nomatch h
  | _, _, _, .lit .., h => nomatch h
  | _, _, _, .refl .., h => nomatch h
  | _, _, _, .symm .., h => nomatch h
  | _, _, _, .trans .., h => nomatch h

theorem Flat.bPrefixW_of_bPrefix : {A B : Expr Nat} →
    (f : Flat R Γ A B) → f.bPrefix = true → f.bPrefixW = true
  | _, _, .nil _, _ => rfl
  | _, _, .cons l _ rest, h => by
      have h' : bLink l = true ∧ rest.bPrefix = true := by
        simpa only [Flat.bPrefix, Bool.and_eq_true] using h
      simp only [Flat.bPrefixW, Bool.and_eq_true]
      exact ⟨bLinkW_of_bLink l h'.1, rest.bPrefixW_of_bPrefix h'.2⟩

theorem Flat.segAdmW_of_segAdm : {P M : Expr Nat} → (p : Flat R Γ P M) →
    p.segAdm = true → p.segAdmW = true
  | _, _, .nil _, _ => rfl
  | _, _, .cons l _ (.nil _), h => by
      have h' : (piSpinedTc l || bLink l) = true := by
        simpa only [Flat.segAdm] using h
      cases hp : piSpinedTc l with
      | true => simp only [Flat.segAdmW, hp, Bool.true_or]
      | false =>
          rw [hp, Bool.false_or] at h'
          simp only [Flat.segAdmW, hp, Bool.false_or]
          exact bLinkW_of_bLink l h'
  | _, _, .cons l _ (.cons l' hl' rest'), h => by
      have h' : bLink l = true ∧ (Flat.cons l' hl' rest').bPrefix = true := by
        simpa only [Flat.segAdm, Bool.and_eq_true] using h
      simp only [Flat.segAdmW, Bool.and_eq_true]
      exact ⟨bLinkW_of_bLink l h'.1,
        (Flat.cons l' hl' rest').bPrefixW_of_bPrefix h'.2⟩

theorem Segs.admW_of_adm : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    s.adm = true → s.admW = true
  | _, _, .nil _, _ => rfl
  | _, _, .cons p _ rest, h => by
      have h' : p.segAdm = true ∧ rest.adm = true := by
        simpa only [Segs.adm, Bool.and_eq_true] using h
      simp only [Segs.admW, Bool.and_eq_true]
      exact ⟨p.segAdmW_of_segAdm h'.1, rest.admW_of_adm h'.2⟩

theorem xAdmW_of_xAdm {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) :
    xAdm c = true → xAdmW c = true :=
  Segs.admW_of_adm _

/-- the W-X-WK flip, against the landed `pin_bLink_wk_succ_false`: a
    weakening at any cutoff is now a valley link when its body is. -/
theorem bLinkW_wk (d : LocalDecl) (k : Nat) {A B : Expr Nat}
    (l : EvTc R Γ A B) : bLinkW (EvTc.wk d k l) = bLinkW l := rfl

/-- W-X-SUBST stays refused here (WK-2 + PR-B admits it): an `esub`
    conversion is never a W valley literal. -/
theorem bCvW_esub {Γ : LCtx} {a b T t v : Expr Nat} (j : Nat) (u : Level)
    (h : EvCv R Γ a b T) (hget : Γ[j]? = some (.assumption t))
    (hv : EvTy R (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (hvT : EvTy R (substRemove v j Γ) (lift 0 j t) (.sort u)) :
    bCvW (EvCv.esub j u h hget hv hvT) = false := rfl

/-! ### §3 the supplier bundle (Q3: Via J; Q4: context-conditioned D) -/

/-- H-D, partial and context-conditioned (Q4): the diamond on provenance
    stars at a common index in a context certified well-formed by the
    CALLER, or a refusal. -/
abbrev DProcWfP (R : List (Jd E n)) : Type :=
  ∀ {Γ : LCtx} {a b c T : Expr Nat}, CtxWfT E n Γ →
    EvParStar R Γ a b T → EvParStar R Γ a c T →
    Option (Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T)

/-- `DContractWfP`'s clause: same as `DContractP` with the `hΓ` argument
    threaded. -/
def DContractWfP (D : ∀ R : List (Jd E n), DProcWfP R) : Prop :=
  ∀ R {Γ : LCtx} {a b c T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T)
    (r : Σ' d : Expr Nat, EvParStar R Γ b d T × EvParStar R Γ c d T),
    D R hΓ h₁ h₂ = some r → ∀ ℓ ∈ r.2.1.leaves ++ r.2.2.leaves,
      ∃ ℓ' ∈ h₁.leaves ++ h₂.leaves, SubEq ℓ ℓ'

/-- a total context-conditional supplier is a partial one. -/
def DProcWfP.ofTotal (D : ∀ R : List (Jd E n), DProcWf R) :
    ∀ R : List (Jd E n), DProcWfP R :=
  fun R {_ _ _ _ _} hΓ h₁ h₂ => some (D R hΓ h₁ h₂)

theorem DContractWfP.ofTotal {D : ∀ R : List (Jd E n), DProcWf R}
    (hD : DContractWf D) : DContractWfP (DProcWfP.ofTotal D) := by
  intro R Γ a b c T hΓ h₁ h₂ r hr
  simp only [DProcWfP.ofTotal, Option.some.injEq] at hr
  subst hr
  exact hD R hΓ h₁ h₂

/-- TOOTH (Q4): the `CtxWfT` premise is forwarded, never invented. -/
theorem DProcWfP.ofTotal_eq (D : ∀ R : List (Jd E n), DProcWf R)
    {Γ : LCtx} {a b c T : Expr Nat} (hΓ : CtxWfT E n Γ)
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    DProcWfP.ofTotal D R hΓ h₁ h₂ = some (D R hΓ h₁ h₂) := rfl

/-- a premise-free partial supplier ignores the context certificate. -/
def DProcP.toWfP (D : ∀ R : List (Jd E n), DProcP R) :
    ∀ R : List (Jd E n), DProcWfP R :=
  fun R {_ _ _ _ _} _ h₁ h₂ => D R h₁ h₂

theorem DContractP.toWfP {D : ∀ R : List (Jd E n), DProcP R}
    (hD : DContractP D) : DContractWfP (DProcP.toWfP D) := by
  intro R Γ a b c T hΓ h₁ h₂ r hr
  exact hD R h₁ h₂ r hr

/-- D1's `dProcWf` as a supplier (Q4): it is exactly a `DProcWf`. -/
def d1WfP (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    ∀ R : List (Jd E n), DProcWfP R :=
  DProcWfP.ofTotal (fun R => dProcWf (R := R) hW su)

theorem d1WfP_contract (hW : EnvWfT E) (su : F8A2Support.SortUnique E n) :
    DContractWfP (d1WfP hW su) :=
  DContractWfP.ofTotal (dContractWf hW su)

/-! #### the ViaS J lift (WK-2 premise)

J re-fronted on `CtxWfViaS`: the worker is then re-enterable at a
context reached by a `CtxMorph` stack — slice 2 (W-X-SUBST, #7207)
re-enters it at a substitution's SOURCE context. The D-side ViaS front
(`DProcViaSP`/`DContractViaSP`/`DProcViaSP.toWfP`) is D-owned and lives
in `RcicF8DViaSSupply` (#7277, which imports THIS module — so it cannot
be imported back); the `Wf`-front→ViaS lift `DProcWfP.toViaSP` and the
`SuppliersViaS` bundle layer therefore live in `RcicF8XValleyViaS`. A
landed Via-front J lifts to the ViaS front only PARTIALLY:
`JProcViaP.toViaSP` answers insertion-only stacks (recovered by
`CtxMorph.toWk?`); the refusals are honest (`JProcViaP.toViaSP_sub_none`)
and the lift is faithful on every witness the `ofWf` route builds
(`JProcViaP.toViaSP_viaS`). -/

/-- the weakening image of an `ins`-only stack; `sub`/`subLet` have
    none. Declared inside `CtxMorph`'s own namespace so `σ.toWk?`
    resolves on `CtxMorph` terms (`_root_` pins the name — an `Rcic`
    namespace under `F8Measure` would otherwise shadow it). -/
def _root_.Rcic.Declarative.CtxMorph.toWk? : {Γ₀ Γ' : LCtx} →
    CtxMorph E n Γ₀ Γ' → Option (Wk Γ₀ Γ')
  | _, _, .nil => some (Wk.id _)
  | _, _, .ins d c σ => (CtxMorph.toWk? σ).map (Wk.ins d c)
  | _, _, .sub .. => none
  | _, _, .subLet .. => none

/-- `toWk?` inverts `Wk.toCtxMorph`. -/
theorem Wk.toCtxMorph_toWk? : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    (Wk.toCtxMorph ρ : CtxMorph E n Γ₀ Γ').toWk? = some ρ
  | _, _, .id _ => rfl
  | _, _, .ins d k ρ => by
      simp only [Wk.toCtxMorph, CtxMorph.toWk?, Wk.toCtxMorph_toWk? ρ,
        Option.map]

/-- pull a ViaS witness at `Γ'` back along a weakening `ρ : Wk Γ₀ Γ'` —
    the witness at the `wk` node's own context, built from the segment
    context's well-formedness. -/
def Wk.viaS : {Γ₀ Γ' : LCtx} → Wk Γ₀ Γ' → CtxWfViaS E n Γ' →
    CtxWfViaS E n Γ₀
  | _, _, .id _, v => v
  | _, _, .ins d k ρ, v => CtxWfViaS.ins d k (ρ.viaS v)

/-- `viaS` on `ofWf` is `ofStack` of `toCtxMorph`. -/
theorem Wk.viaS_ofWf : {Γ₀ Γ' : LCtx} → (ρ : Wk Γ₀ Γ') →
    (hΓ' : CtxWfT E n Γ') →
    ρ.viaS (.ofWf hΓ') = (⟨Γ', ρ.toCtxMorph, hΓ'⟩ : CtxWfViaS E n Γ₀)
  | _, _, .id _, _ => rfl
  | _, _, .ins d k ρ, hΓ' => by
      rw [Wk.viaS, Wk.toCtxMorph, CtxWfViaS.ins, Wk.viaS_ofWf ρ hΓ']

/-- the stack `viaS` builds on `ofWf` is `ρ`'s `CtxMorph` image —
    `HEq` because `(ρ.viaS v).target` is a stuck projection for an open
    `ρ`; rewrite the witness with `Wk.viaS_ofWf` and project where a
    homogeneous equation is needed. -/
theorem Wk.viaS_σ {Γ₀ Γ' : LCtx} (ρ : Wk Γ₀ Γ') (hΓ' : CtxWfT E n Γ') :
    HEq (ρ.viaS (.ofWf hΓ')).σ (ρ.toCtxMorph : CtxMorph E n Γ₀ Γ') := by
  rw [Wk.viaS_ofWf ρ hΓ']

/-- a landed Via-front J lifts to the ViaS front only PARTIALLY: the
    stack is recovered as a `Wk` by `CtxMorph.toWk?`, so `ins`-only
    witnesses are answered through the Via supplier and `sub`/`subLet`
    refused. -/
def JProcViaP.toViaSP (J : ∀ R : List (Jd E n), JProcViaP R) :
    ∀ R : List (Jd E n), JProcViaSP R :=
  fun R {_ _ _ _} v h hs =>
    match v.σ.toWk? with
    | some ρ => J R ⟨v.target, ρ, v.wf⟩ h hs
    | none => none

/-- the strict clause survives the partial lift. -/
theorem JContractViaP.toViaSP {J : ∀ R : List (Jd E n), JProcViaP R}
    (hJ : JContractViaP J) : JContractViaSP (JProcViaP.toViaSP J) := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  unfold JProcViaP.toViaSP at hV
  split at hV
  · next ρ hρ => exact hJ R ⟨v.target, ρ, v.wf⟩ h hsub V hV
  · next hρ => exact Option.noConfusion hV

/-- TOOTH: a Via-front J cannot answer a substituted witness — `sub`
    has no `Wk` image, so the lift refuses. -/
theorem JProcViaP.toViaSP_sub_none (J : ∀ R : List (Jd E n), JProcViaP R)
    {Γ : LCtx} {t v : Expr Nat} (j : Nat)
    (hget : Γ[j]? = some (.assumption t))
    (hv : HasTyT E n (substRemove v j Γ) (lift 0 j v) (lift 0 j t))
    (w : CtxWfViaS E n (substRemove v j Γ)) {M₁ M₂ T : Expr Nat}
    (h : ConvT E n Γ M₁ M₂ T) (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    JProcViaP.toViaSP J R (CtxWfViaS.sub j hget hv w) h hs = none := rfl

/-- faithfulness: on every witness the `ofWf`-through-`viaS` route
    builds, the lifted J answers exactly as the Via supplier on the
    `Wk` witness. -/
theorem JProcViaP.toViaSP_viaS (J : ∀ R : List (Jd E n), JProcViaP R)
    {Γ₀ Γ' : LCtx} (ρ : Wk Γ₀ Γ') (hΓ' : CtxWfT E n Γ')
    {M₁ M₂ T : Expr Nat} (h : ConvT E n Γ₀ M₁ M₂ T)
    (hs : ∃ r ∈ R, SubEq (.cv h) r) :
    JProcViaP.toViaSP J R (ρ.viaS (.ofWf hΓ')) h hs =
      J R ⟨Γ', ρ, hΓ'⟩ h hs := by
  unfold JProcViaP.toViaSP
  rw [Wk.viaS_ofWf ρ hΓ']
  simp only [Wk.toCtxMorph_toWk? ρ]

/-- the WK-1b supplier bundle: J is `Via`-premised (Q3), D is
    context-conditioned (Q4); K/hsep/U/S are the landed fields. -/
structure SuppliersVia (E : ResolvedEnv) (n : Nat) where
  K : ∀ R : List (Jd E n), CtxConvProc R
  hK : CtxConvContract K
  hsep : SepAll E n
  J : ∀ R : List (Jd E n), JProcViaP R
  hJ : JContractViaP J
  D : ∀ R : List (Jd E n), DProcWfP R
  hD : DContractWfP D
  U : ∀ R : List (Jd E n), UProcP R
  hU : UContractP U
  S : ∀ R : List (Jd E n), StructPiProcP R
  hS : StructPiContractP S

/-- the landed bundle AT a segment context: J through `.ofWf`; D answers
    only at `Γ'`, with the given `hΓ'`, and refuses elsewhere; U/S/K as
    is. This is what the landed `scombine`/`sjoin`/`sread`/`SegOut.comp`
    receive. -/
def SuppliersVia.atSeg (X : SuppliersVia E n) {Γ' : LCtx}
    (hΓ' : CtxWfT E n Γ') : Suppliers E n where
  K := X.K
  hK := X.hK
  hsep := X.hsep
  J := JProcViaP.toWfP X.J
  hJ := JContractViaP.toWfP X.hJ
  D := fun R {Γ} {_ _ _ _} h₁ h₂ =>
    if h : Γ = Γ' then X.D R (h.symm ▸ hΓ') h₁ h₂ else none
  hD := by
    intro R Γ a b c T h₁ h₂ r hr
    dsimp only at hr
    split at hr
    · next h =>
        subst h
        exact X.hD R hΓ' h₁ h₂ r hr
    · next h => exact Option.noConfusion hr
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-- at the segment context itself `atSeg`'s D is `X.D` at `hΓ'`. -/
theorem SuppliersVia.atSeg_D_eq (X : SuppliersVia E n)
    (hΓ' : CtxWfT E n Γ') {a b c T : Expr Nat} (h₁ : EvParStar R Γ' a b T)
    (h₂ : EvParStar R Γ' a c T) :
    (X.atSeg hΓ').D R h₁ h₂ = X.D R hΓ' h₁ h₂ := by
  show (if h : Γ' = Γ' then X.D R (h.symm ▸ hΓ') h₁ h₂ else none) = X.D R hΓ' h₁ h₂
  exact dif_pos rfl

/-- TOOTH (Q4): `atSeg`'s D is answered only where its `CtxWfT` is
    real — elsewhere it refuses. -/
theorem SuppliersVia.atSeg_D_ne (X : SuppliersVia E n)
    (hΓ' : CtxWfT E n Γ') {Γ : LCtx} (hne : Γ ≠ Γ') {a b c T : Expr Nat}
    (h₁ : EvParStar R Γ a b T) (h₂ : EvParStar R Γ a c T) :
    (X.atSeg hΓ').D R h₁ h₂ = none := by
  show (if h : Γ = Γ' then X.D R (h.symm ▸ hΓ') h₁ h₂ else none) = none
  exact dif_neg hne

/-- the declining Via bundle: the landed `ctxConvVar` as K, every
    J/D/U/S request declined. -/
def SuppliersVia.declining (hsep : SepAll E n) : SuppliersVia E n where
  K := fun _ {_ _ _ _ _} cA e => ctxConvVar cA e
  hK := fun _ {_ _ _ _ _} cA e => ctxConvVar_contract cA e
  hsep := hsep
  J := fun _ {_ _ _ _} _ _ _ => none
  hJ := fun _ {_ _ _ _} _ _ _ _ h => nomatch h
  D := fun _ {_ _ _ _ _} _ _ _ => none
  hD := fun _ {_ _ _ _ _} _ _ _ _ h => nomatch h
  U := fun _ {_ _ _ _} _ _ => none
  hU := fun _ {_ _ _ _} _ _ _ h => nomatch h
  S := fun _ {_ _ _ _ _} _ => none
  hS := fun _ {_ _ _ _ _} _ _ h => nomatch h

/-- every landed bundle lifts to a Via bundle, given a Via-capable J; a
    landed `JProcWfP` CANNOT be lifted — that is the point (the `Via`
    premise is strictly weaker). -/
def SuppliersVia.withJ (X : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaP R) (hJ : JContractViaP J) :
    SuppliersVia E n where
  K := X.K
  hK := X.hK
  hsep := X.hsep
  J := J
  hJ := hJ
  D := DProcP.toWfP X.D
  hD := DContractP.toWfP X.hD
  U := X.U
  hU := X.hU
  S := X.S
  hS := X.hS

/-! ### §4 the push-to-literal worker, on the WK-2 premise

Every arm mirrors #7142's `svalleyCv`/`slinkValley` arm; the `.wk` arm
folds into the pending morphism and recurses at EVERY cutoff. The
premise is `CtxWfViaS` (WK-2): the worker is re-enterable at ANY
context — slice 2 (W-X-SUBST, #7207) re-enters it at a substitution's
source context. The shared engine fixes separation-free
`ValleyOps` at the actual call context, with a real `JProcViaSP` and its
contract and a structural runner. Main's public `Suppliers` + J front
forgets to those operations and uses global separation for its runner.
The conditional front in `RcicF8XValleyViaS` supplies `atOps v` and the
WK-2 structural runner. Its explicit-SepAll `atCtx` view agrees with
`atOps` after forgetting separation. The landed `…Via` names remain
the `ofWf` instances. There is ONE worker body. -/

/-- Compatibility view of J and context-specific operations.
    D's ViaS interface is owned by the higher RcicF8DViaSSupply module. -/
structure ViaSCore (E : ResolvedEnv) (n : Nat) where
  J : ∀ R : List (Jd E n), JProcViaSP R
  hJ : JContractViaSP J
  atOps : ∀ {Γ : LCtx}, CtxWfViaS E n Γ → ValleyOps E n

/-- The old bundle's operational view. Its D answers only at the matching
    context and an empty morphism stack; other witnesses honestly refuse. -/
def SuppliersVia.core (X : SuppliersVia E n) : ViaSCore E n where
  J := JProcViaP.toViaSP X.J
  hJ := JContractViaP.toViaSP X.hJ
  atOps := fun {Γ'} v => {
    K := X.K
    hK := X.hK
    D := fun R {Γ} {_ _ _ _} h₁ h₂ =>
      if h : Γ = Γ' then
        match h.symm ▸ v with
        | ⟨_, .nil, wf⟩ => X.D R wf h₁ h₂
        | _ => none
      else none
    hD := by
      intro R Γ a b c T h₁ h₂ r hr
      dsimp only at hr
      split at hr
      · next h =>
          subst h
          obtain ⟨target, σ, wf⟩ := v
          cases σ <;> first
            | exact Option.noConfusion hr
            | exact X.hD R wf h₁ h₂ r hr
      · exact Option.noConfusion hr
    U := X.U
    hU := X.hU
    S := X.S
    hS := X.hS }

abbrev XStructRunnerViaS (E : ResolvedEnv) (n : Nat) :=
  ∀ (R : List (Jd E n)) {Γ : LCtx} {A B A₁ B₁ A₂ B₂ : Expr Nat},
    CtxWfViaS E n Γ → (c : EvTc R Γ A B) → piSpinedTc c = true →
    A = .pi A₁ B₁ → B = .pi A₂ B₂ →
    Σ' o : XOut R Γ A₁ B₁ A₂ B₂, ∀ ℓ ∈ XOut.leaves o,
      ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ'

def SuppliersVia.structRunner (X : SuppliersVia E n) : XStructRunnerViaS E n :=
  fun _ {_ _ _ _ _ _ _} _ c hp ha hb =>
    ⟨xStructTc X.K X.hK X.hsep c hp ha hb,
      xStructTc_leaves X.K X.hK X.hsep c hp ha hb⟩

/-- Global-separation runner for the landed public interface. -/
def Suppliers.structRunnerViaS (XS : Suppliers E n) : XStructRunnerViaS E n :=
  fun _ {_ _ _ _ _ _ _} _ c hp ha hb =>
    ⟨xStructTc XS.K XS.hK XS.hsep c hp ha hb,
      xStructTc_leaves XS.K XS.hK XS.hsep c hp ha hb⟩

namespace ViaSEngine
def svalleyCvViaS (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) : {Γ₀ Γ' : LCtx} →
    {a b T : Expr Nat} → (c : EvCv R Γ₀ a b T) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bCvW c = true →
    Option (SOutB R Γ' (ρ.map a) (ρ.map b) (ρ.map T) c.leaves)
  | _, Γ', _, _, _, .lit h hsub, ρ, v, _ =>
      match he : J R (ρ.viaS v) h hsub with
      | none => none
      | some V =>
          -- DEEP thinning (audit P2): `V.thin ρ` would wrap J's stars in
          -- lazy `EvParStar.wk`, and `readStarC` would then call `X.S` on
          -- the unwrapped SOURCE-context steps. `thinDeep` pushes `ρ`
          -- into each step's payload, so S runs at `Γ'`.
          -- Q92: `subst0`/`substLet` do not commute. `thinDeep` reifies
          -- them by `thinWk`, and the inherited reader would then call
          -- `X.S` in the SOURCE context. Refuse before that reader runs.
          -- Slice 2 (#7207) re-enters substitution at segment level.
          match Valley.admitSubst true V with
          | none => none
          | some _ =>
          some ⟨(⟨.val (V.thinDeep ρ) (.refl _ _), [], [.cv h]⟩ :
              SOut R Γ' _ _ _),
            by
              refine ⟨fun ℓ hℓ => ⟨.cv h, ?_,
                    hJ R (ρ.viaS v) h hsub V he ℓ
                      (Valley.thinDeep_leaves ρ V ▸
                        (hℓ : ℓ ∈ (V.thinDeep ρ).leaves))⟩,
                fun C hC => absurd hC (List.not_mem_nil _),
                fun j hj => ?_, fun j hj => ?_,
                fun _ => List.cons_ne_nil _ _,
                fun hne => absurd rfl hne,
                fun ℓ hℓ => absurd hℓ (List.not_mem_nil _)⟩
              · simp only [EvCv.leaves, List.mem_cons, List.not_mem_nil,
                  or_false]
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                subst hj
                exact ⟨.cv h, by simp only [EvCv.leaves, List.mem_cons,
                    List.not_mem_nil, or_false], .inl rfl⟩
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
                subst hj
                exact ⟨_, _, _, _, h, rfl⟩⟩
  | _, _, _, _, _, .refl D, ρ, v, _ =>
      some ⟨(⟨.triv D (.refl _ _), [], []⟩ : SOut R _ _ _ _).thin ρ,
        SOut.bound_thin ρ (SOut.bound_triv D _ (fun ℓ hℓ =>
          below_of_mem hℓ))⟩
  | _, _, _, _, _, .symm c, ρ, v, h =>
      (svalleyCvViaS XS J hJ run c ρ v (by simpa only [bCvW] using h)).map (fun r =>
        ⟨r.1.symm,
          SOut.bound_of_eq (SOut.bound_symm r.2) (by simp only [EvCv.leaves])⟩)
  | _, _, _, _, _, .trans c₁ c₂, ρ, v, h =>
      have h' : bCvW c₁ = true ∧ bCvW c₂ = true := by
        simpa only [bCvW, Bool.and_eq_true] using h
      match svalleyCvViaS XS J hJ run c₁ ρ v h'.1, svalleyCvViaS XS J hJ run c₂ ρ v h'.2 with
      | some r₁, some r₂ =>
          (ValleyOps.scombine XS r₁.1 r₁.2 r₂.1 r₂.2).map (fun r =>
            r.elim (fun r => ⟨r.1, SOut.bound_of_eq r.2
                (by simp only [EvCv.leaves])⟩)
              (fun r => ⟨r.1, SOut.bound_of_eq r.2
                (by simp only [EvCv.leaves])⟩))
      | _, _ => none
  | _, _, _, _, _, .tyConv u' c cA, ρ, v, h =>
      (svalleyCvViaS XS J hJ run c ρ v (by simpa only [bCvW] using h)).map (fun r =>
        ⟨r.1.rety (.ofCv u' (EvCv.castIdx (ρ.map_sort u')
            (EvCv.thin ρ cA))),
          SOut.bound_of_eq (SOut.bound_rety r.2
            (.ofCv u' (EvCv.castIdx (ρ.map_sort u') (EvCv.thin ρ cA))))
            (by simp only [EvCv.leaves, EvTc.leaves, EvCv.castIdx_leaves,
              EvCv.thin_leaves])⟩)
  | _, _, _, _, _, @EvCv.wk _ _ _ Γ₁ a₀ b₀ T₀ d k c, ρ, v, h =>
      svalleyCvViaS XS J hJ run c (.ins d k ρ) v (by simpa only [bCvW] using h)
  | _, _, _, _, _, .esub .., _, _, h => nomatch h
  | _, _, _, _, _, .subst0 .., _, _, h => nomatch h
  | _, _, _, _, _, .substLet .., _, _, h => nomatch h
  | _, _, _, _, _, .sorts .., _, _, h => nomatch h
  | _, _, _, _, _, .consts .., _, _, h => nomatch h
  | _, _, _, _, _, .rety c cA, ρ, v, h =>
      (svalleyCvViaS XS J hJ run c ρ v (by simpa only [bCvW] using h)).map (fun r =>
        ⟨r.1.rety (EvTc.thin ρ cA),
          SOut.bound_of_eq (SOut.bound_rety r.2 (EvTc.thin ρ cA))
            (by simp only [EvCv.leaves, EvTc.thin_leaves])⟩)

/-- a link's valley at the segment context, index selected by that
    link. -/
def slinkValleyViaS (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) : {Γ₀ Γ' : LCtx} →
    {A B : Expr Nat} → (l : EvTc R Γ₀ A B) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bLinkW l = true →
    Option (Σ T : Expr Nat, SOutB R Γ' (ρ.map A) (ρ.map B) T l.leaves)
  | _, _, _, _, .ofCv u c, ρ, v, hb =>
      (svalleyCvViaS XS J hJ run c ρ v (by simpa only [bLinkW] using hb)).map
        (fun r => ⟨ρ.map (.sort u), r.1,
          SOut.bound_of_eq r.2 (by simp only [EvTc.leaves])⟩)
  | _, _, _, _, @EvTc.wk _ _ _ Γ₁ A₀ B₀ d k l, ρ, v, hb =>
      slinkValleyViaS XS J hJ run l (.ins d k ρ) v (by simpa only [bLinkW] using hb)
  | _, _, _, _, .piCod .., _, _, hb => nomatch hb
  | _, _, _, _, .subst0 .., _, _, hb => nomatch hb
  | _, _, _, _, .substLet .., _, _, hb => nomatch hb
  | _, _, _, _, .lit .., _, _, hb => nomatch hb
  | _, _, _, _, .refl .., _, _, hb => nomatch hb
  | _, _, _, _, .symm .., _, _, hb => nomatch hb
  | _, _, _, _, .trans .., _, _, hb => nomatch hb

/-- a heterogeneous prefix keeps the demanded index of the selected
    nontrivial side, at the segment context. -/
def sprefixValleyViaS (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) (v : CtxWfViaS E n Γ) :
    {P M B : Expr Nat} → (l : EvTc R Γ P M) → bLinkW l = true →
    (rest : Flat R Γ M B) → rest.bPrefixW = true →
    Option (Σ T : Expr Nat, SOutB R Γ P B T (l.leaves ++ rest.leaves))
  | _, _, _, l, hb, .nil _, _ =>
      (slinkValleyViaS XS J hJ run l (Wk.id Γ) v hb).map (fun r =>
        ⟨r.1, r.2.1, SOut.bound_left r.2.2⟩)
  | _, _, _, l, hb, .cons l' hl' rest', hb' =>
      have h' : bLinkW l' = true ∧ rest'.bPrefixW = true := by
        simpa only [Flat.bPrefixW, Bool.and_eq_true] using hb'
      match slinkValleyViaS XS J hJ run l (Wk.id Γ) v hb,
          sprefixValleyViaS XS J hJ run v l' h'.1 rest' h'.2 with
      | some r₁, some r₂ =>
          (ValleyOps.scombine XS r₁.2.1 r₁.2.2 r₂.2.1 r₂.2.2).map (fun r =>
            r.elim (fun r => ⟨r₁.1, r.1, SOut.bound_of_eq r.2
                (by simp only [Flat.leaves])⟩)
              (fun r => ⟨r₂.1, r.1, SOut.bound_of_eq r.2
                (by simp only [Flat.leaves])⟩))
      | _, _ => none

/-- X on one segment under the W fragment, with the census; or a
    refusal. A single Π-spined link is Stratum A: no call. -/
def xSegSViaS (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) (v : CtxWfViaS E n Γ) :
    {P M : Expr Nat} → (p : Flat R Γ P M) → p.segAdmW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (SegOut R Γ A B A' B' p.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hM =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hM
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves,
            List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, .cons l hl (.nil _), hadm, A, B, A', B', hP, hM =>
      if hp : piSpinedTc l = true then
        some (SegOut.ofA ((run R v l hp hP hM).1)
          (fun ℓ hℓ => by
            simp only [Flat.leaves, List.append_nil]
            exact (run R v l hp hP hM).2 ℓ hℓ))
      else
        have hb : bLinkW l = true := by
          have h' : (piSpinedTc l || bLinkW l) = true := by
            simpa only [Flat.segAdmW] using hadm
          simpa only [Bool.or_eq_true, hp, Bool.false_eq_true,
            false_or] using h'
        match slinkValleyViaS XS J hJ run l (Wk.id Γ) v hb with
        | none => none
        | some ⟨_, o, ho⟩ =>
            ValleyOps.sread XS o (SOut.bound_of_eq ho
              (by simp only [Flat.leaves, List.append_nil])) hP hM
  | _, _, .cons l hl (.cons l' hl' rest'), hadm, A, B, A', B', hP, hM =>
      have h' : bLinkW l = true ∧ (Flat.cons l' hl' rest').bPrefixW = true := by
        simpa only [Flat.segAdmW, Bool.and_eq_true] using hadm
      match sprefixValleyViaS XS J hJ run v l h'.1 (Flat.cons l' hl' rest') h'.2 with
      | none => none
      | some ⟨_, o, ho⟩ =>
          ValleyOps.sread XS o (SOut.bound_of_eq ho
            (by simp only [Flat.leaves])) hP hM

/-- X on the segments under the W fragment, with the census; or a
    refusal. -/
def xSegsViaS (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) (v : CtxWfViaS E n Γ) :
    {P Q : Expr Nat} → (s : Segs R Γ P Q) → s.admW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (SegOut R Γ A B A' B' s.leaves)
  | _, _, .nil _, _, A, B, A', B', hP, hQ =>
      have e : (Expr.pi A B : Expr Nat) = .pi A' B' := hP.symm.trans hQ
      some (SegOut.ofA (EvTc.cast rfl rfl (Expr.pi.inj e).1 (.refl _ _),
        EvTc.cast rfl rfl (Expr.pi.inj e).2 (.refl _ _)) (fun ℓ hℓ => by
          simp only [XOut.leaves, EvTc.cast_leaves, EvTc.leaves,
            List.append_nil, List.not_mem_nil] at hℓ))
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, A, B, A', B', hP, hQ =>
      have h' : p.segAdmW = true ∧ rest.admW = true := by
        simpa only [Segs.admW, Bool.and_eq_true] using hadm
      match isPiD M hM with
      | ⟨A₁, B₁, hM'⟩ =>
        match xSegSViaS XS J hJ run v p h'.1 hP hM',
            xSegsViaS XS J hJ run v rest h'.2 hM' hQ with
        | some r₁, some r₂ =>
            some (SegOut.cast (by simp only [Segs.leaves])
              (ValleyOps.comp XS r₁ r₂))
        | _, _ => none

/-- the ViaS X route on a W-admissible input: components, U/D/S
    bundles, J literals, bounds; or a refusal. -/
def xValleySViaS? (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n) (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  (xSegsViaS XS J hJ run v ((flattenTc c).segment rfl) hadm rfl rfl).map (fun r => by
    obtain ⟨o, calls, jcalls, h1, h2, h3, h4, h5⟩ := r
    rw [Flat.segment_leaves] at h1 h2 h3
    exact ⟨o, calls, jcalls, fun ℓ hℓ =>
        below_trans (h1 ℓ hℓ) (flattenTc_leaves c),
      fun C hC ℓ hℓ =>
        strict_of_strict_below (h2 C hC ℓ hℓ) (flattenTc_leaves c),
      fun j hj => below_trans (h3 j hj) (flattenTc_leaves c), h4, h5⟩)

end ViaSEngine

namespace ViaSEngine
theorem xSegSViaS_isSome_of_spined (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n)
    (v : CtxWfViaS E n Γ) {P M : Expr Nat} (l : EvTc R Γ P M)
    (hl : isLink l = true)
    (hadm : (Flat.cons l hl (Flat.nil M)).segAdmW = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat}
    (hP : P = .pi A B) (hM : M = .pi A' B') :
    (xSegSViaS XS J hJ run v (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome =
      true := by
  rw [xSegSViaS, dif_pos hp]
  rfl

theorem xSegsViaS_isSome_of_stratumA (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n)
    (v : CtxWfViaS E n Γ) : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    (hadm : s.admW = true) → s.stratumA = true →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    (xSegsViaS XS J hJ run v s hadm hP hQ).isSome = true
  | _, _, .nil _, _, _, A, B, A', B', hP, hQ => rfl
  | _, _, @Segs.cons _ _ _ _ P M Q p hM rest, hadm, hsA, A, B, A', B',
      hP, hQ => by
      cases p with
      | nil _ => simp only [Segs.stratumA, Bool.false_eq_true] at hsA
      | cons l hl rest' =>
          cases rest' with
          | cons _ _ _ =>
              simp only [Segs.stratumA, Bool.false_eq_true] at hsA
          | nil _ =>
              simp only [Segs.stratumA, Bool.and_eq_true] at hsA
              obtain ⟨hp, hsA'⟩ := hsA
              have h' : (Flat.cons l hl (Flat.nil M)).segAdmW = true ∧
                  rest.admW = true := by
                simpa only [Segs.admW, Bool.and_eq_true] using hadm
              obtain ⟨A₁, B₁, hM'⟩ := isPi_true hM
              have h1 := xSegSViaS_isSome_of_spined XS J hJ run v l hl h'.1 hp hP hM'
              have h2 := xSegsViaS_isSome_of_stratumA XS J hJ run v rest h'.2 hsA'
                hM' hQ
              subst hM'
              rw [xSegsViaS]
              simp only [isPiD]
              split
              · rfl
              · rename_i hne
                exfalso
                rcases e1 : xSegSViaS XS J hJ run v (Flat.cons l hl (Flat.nil _))
                  h'.1 hP rfl with _ | r₁
                · rw [e1] at h1; simp at h1
                · rcases e2 : xSegsViaS XS J hJ run v rest h'.2 rfl hQ with _ | r₂
                  · rw [e2] at h2; simp at h2
                  · exact hne r₁ r₂ e1 e2

/-- Stratum A is answered by every ViaS bundle (nothing here is
    vacuous). -/
theorem xValleySViaS?_isSome_of_piSpined (XS : ValleyOps E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (run : XStructRunnerViaS E n)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xValleySViaS? XS J hJ run v c
      (xAdmW_of_xAdm c (xAdm_of_piSpined c hp))).isSome = true := by
  simp only [xValleySViaS?, isSome_map']
  exact xSegsViaS_isSome_of_stratumA XS J hJ run v _ _
    (segmentF_stratumA_of_spined _ (flattenTc c) rfl (Nat.le_refl _)
      (flattenTc_spined c hp rfl rfl))
    rfl rfl

end ViaSEngine

def svalleyCvViaS (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J) :
    {Γ₀ Γ' : LCtx} →
    {a b T : Expr Nat} → (c : EvCv R Γ₀ a b T) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bCvW c = true →
    Option (SOutB R Γ' (ρ.map a) (ρ.map b) (ρ.map T) c.leaves) :=
  ViaSEngine.svalleyCvViaS XS.toValleyOps J hJ XS.structRunnerViaS

/-- a link's valley at the segment context, index selected by that
    link. -/
def slinkValleyViaS (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J) :
    {Γ₀ Γ' : LCtx} →
    {A B : Expr Nat} → (l : EvTc R Γ₀ A B) →
    (ρ : Wk Γ₀ Γ') → (v : CtxWfViaS E n Γ') → bLinkW l = true →
    Option (Σ T : Expr Nat, SOutB R Γ' (ρ.map A) (ρ.map B) T l.leaves) :=
  ViaSEngine.slinkValleyViaS XS.toValleyOps J hJ XS.structRunnerViaS

/-- a heterogeneous prefix keeps the demanded index of the selected
    nontrivial side, at the segment context. -/
def sprefixValleyViaS (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) :
    {P M B : Expr Nat} → (l : EvTc R Γ P M) → bLinkW l = true →
    (rest : Flat R Γ M B) → rest.bPrefixW = true →
    Option (Σ T : Expr Nat, SOutB R Γ P B T (l.leaves ++ rest.leaves)) :=
  ViaSEngine.sprefixValleyViaS XS.toValleyOps J hJ XS.structRunnerViaS v

/-- X on one segment under the W fragment, with the census; or a
    refusal. A single Π-spined link is Stratum A: no call. -/
def xSegSViaS (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) :
    {P M : Expr Nat} → (p : Flat R Γ P M) → p.segAdmW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → M = .pi A' B' →
    Option (SegOut R Γ A B A' B' p.leaves) :=
  ViaSEngine.xSegSViaS XS.toValleyOps J hJ XS.structRunnerViaS v

/-- X on the segments under the W fragment, with the census; or a
    refusal. -/
def xSegsViaS (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) :
    {P Q : Expr Nat} → (s : Segs R Γ P Q) → s.admW = true →
    ∀ {A B A' B' : Expr Nat}, P = .pi A B → Q = .pi A' B' →
    Option (SegOut R Γ A B A' B' s.leaves) :=
  ViaSEngine.xSegsViaS XS.toValleyOps J hJ XS.structRunnerViaS v

/-- the ViaS X route on a W-admissible input: components, U/D/S
    bundles, J literals, bounds; or a refusal. -/
def xValleySViaS? (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  ViaSEngine.xValleySViaS? XS.toValleyOps J hJ XS.structRunnerViaS v c hadm

/-! #### the landed names — the `ofWf` instances of the ViaS worker -/

/-- WK-1b's landed name: the landed bundle AT the segment context plus
    the partial J lift, instantiated at the `ofWf` witness. -/
def svalleyCvVia (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {a b T : Expr Nat} (c : EvCv R Γ₀ a b T) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bCvW c = true) :
    Option (SOutB R Γ' (ρ.map a) (ρ.map b) (ρ.map T) c.leaves) :=
  svalleyCvViaS (X.atSeg hΓ') (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) c ρ (.ofWf hΓ') hb

theorem svalleyCvVia_eq (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {a b T : Expr Nat} (c : EvCv R Γ₀ a b T) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bCvW c = true) :
    svalleyCvVia X c ρ hΓ' hb =
      svalleyCvViaS (X.atSeg hΓ') (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) c ρ (.ofWf hΓ') hb :=
  rfl

/-- WK-1b's landed name: the `ofWf` instance of the ViaS worker. -/
def slinkValleyVia (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {A B : Expr Nat} (l : EvTc R Γ₀ A B) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bLinkW l = true) :
    Option (Σ T : Expr Nat, SOutB R Γ' (ρ.map A) (ρ.map B) T l.leaves) :=
  slinkValleyViaS (X.atSeg hΓ') (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) l ρ (.ofWf hΓ') hb

theorem slinkValleyVia_eq (X : SuppliersVia E n) {Γ₀ Γ' : LCtx}
    {A B : Expr Nat} (l : EvTc R Γ₀ A B) (ρ : Wk Γ₀ Γ')
    (hΓ' : CtxWfT E n Γ') (hb : bLinkW l = true) :
    slinkValleyVia X l ρ hΓ' hb =
      slinkValleyViaS (X.atSeg hΓ') (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) l ρ (.ofWf hΓ') hb :=
  rfl

/-- WK-1b's landed name: the `ofWf` instance of the ViaS worker. -/
def sprefixValleyVia (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P M B : Expr Nat} (l : EvTc R Γ P M) (hb : bLinkW l = true)
    (rest : Flat R Γ M B) (hb' : rest.bPrefixW = true) :
    Option (Σ T : Expr Nat, SOutB R Γ P B T (l.leaves ++ rest.leaves)) :=
  sprefixValleyViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) l hb rest hb'

theorem sprefixValleyVia_eq (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {P M B : Expr Nat} (l : EvTc R Γ P M)
    (hb : bLinkW l = true) (rest : Flat R Γ M B)
    (hb' : rest.bPrefixW = true) :
    sprefixValleyVia X hΓ l hb rest hb' =
      sprefixValleyViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) l hb rest hb' := rfl

/-- WK-1b's landed name: the `ofWf` instance of the ViaS worker. -/
def xSegSVia (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P M : Expr Nat} (p : Flat R Γ P M) (hadm : p.segAdmW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') :
    Option (SegOut R Γ A B A' B' p.leaves) :=
  xSegSViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) p hadm hP hM

theorem xSegSVia_eq (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P M : Expr Nat} (p : Flat R Γ P M) (hadm : p.segAdmW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hM : M = .pi A' B') :
    xSegSVia X hΓ p hadm hP hM =
      xSegSViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) p hadm hP hM :=
  rfl

/-- WK-1b's landed name: the `ofWf` instance of the ViaS worker. -/
def xSegsSVia (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P Q : Expr Nat} (s : Segs R Γ P Q) (hadm : s.admW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    Option (SegOut R Γ A B A' B' s.leaves) :=
  xSegsViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) s hadm hP hQ

theorem xSegsSVia_eq (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {P Q : Expr Nat} (s : Segs R Γ P Q) (hadm : s.admW = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    xSegsSVia X hΓ s hadm hP hQ =
      xSegsViaS (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) s hadm hP hQ :=
  rfl

/-- WK-1b's landed name: the `ofWf` instance of the ViaS worker. -/
def xValleySVia? (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    Option (SegOut R Γ A B A' B' c.leaves) :=
  xValleySViaS? (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) c hadm

theorem xValleySVia?_eq (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) :
    xValleySVia? X hΓ c hadm =
      xValleySViaS? (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
        (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) c hadm := rfl

/-- `XContractWf`'s clause for every answer of the ViaS route. -/
theorem xValleySViaS_contract (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleySViaS? XS J hJ v c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  r.2.2.2.1

/-- `XContractWf`'s clause for every answer of the Via route — the
    `ofWf` instance of the ViaS statement. -/
theorem xValleySVia_contract (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (hr : xValleySVia? X hΓ c hadm = some r) :
    ∀ ℓ ∈ r.1.1.leaves ++ r.1.2.leaves, ∃ ℓ' ∈ c.leaves, SubEq ℓ ℓ' :=
  xValleySViaS_contract (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) c hadm r hr

/-- the ViaS route's answers carry a lex-edge census — the census
    shape, `EdgeContractLex` and the measure are #7142's, unchanged. -/
theorem xValleySViaS_edges (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (_ : xValleySViaS? XS J hJ v c hadm = some r) (Z : List (Jd E n)) :
    EdgeContractLex (census c r Z) :=
  census_edges c r Z

/-- the Via route's answers carry a lex-edge census — the `ofWf`
    instance of the ViaS statement. -/
theorem xValleySVia_edges (X : SuppliersVia E n) (hΓ : CtxWfT E n Γ)
    {A B A' B' : Expr Nat} (c : EvTc R Γ (.pi A B) (.pi A' B'))
    (hadm : xAdmW c = true) (r : SegOut R Γ A B A' B' c.leaves)
    (hr : xValleySVia? X hΓ c hadm = some r) (Z : List (Jd E n)) :
    EdgeContractLex (census c r Z) :=
  xValleySViaS_edges (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) c hadm r hr Z

/-! Stratum A answers for every `Suppliers`/ViaS-J pair (non-vacuity). -/

theorem xSegSViaS_isSome_of_spined (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) {P M : Expr Nat} (l : EvTc R Γ P M)
    (hl : isLink l = true)
    (hadm : (Flat.cons l hl (Flat.nil M)).segAdmW = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat}
    (hP : P = .pi A B) (hM : M = .pi A' B') :
    (xSegSViaS XS J hJ v (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome =
      true :=
  ViaSEngine.xSegSViaS_isSome_of_spined XS.toValleyOps J hJ XS.structRunnerViaS v l hl hadm hp hP hM

theorem xSegsViaS_isSome_of_stratumA (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) : {P Q : Expr Nat} → (s : Segs R Γ P Q) →
    (hadm : s.admW = true) → s.stratumA = true →
    ∀ {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B'),
    (xSegsViaS XS J hJ v s hadm hP hQ).isSome = true :=
  ViaSEngine.xSegsViaS_isSome_of_stratumA XS.toValleyOps J hJ XS.structRunnerViaS v

/-- Stratum A is answered at every ViaS witness (nothing here is
    vacuous). -/
theorem xValleySViaS?_isSome_of_piSpined (XS : Suppliers E n)
    (J : ∀ R : List (Jd E n), JProcViaSP R) (hJ : JContractViaSP J)
    (v : CtxWfViaS E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xValleySViaS? XS J hJ v c
      (xAdmW_of_xAdm c (xAdm_of_piSpined c hp))).isSome = true :=
  ViaSEngine.xValleySViaS?_isSome_of_piSpined XS.toValleyOps J hJ XS.structRunnerViaS v c hp

/-! and the landed theorem names, derived through the `ofWf` instances -/

theorem xSegSVia_isSome_of_spined (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {P M : Expr Nat} (l : EvTc R Γ P M)
    (hl : isLink l = true)
    (hadm : (Flat.cons l hl (Flat.nil M)).segAdmW = true)
    (hp : piSpinedTc l = true) {A B A' B' : Expr Nat}
    (hP : P = .pi A B) (hM : M = .pi A' B') :
    (xSegSVia X hΓ (Flat.cons l hl (Flat.nil M)) hadm hP hM).isSome =
      true :=
  xSegSViaS_isSome_of_spined (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) l hl hadm hp hP hM

theorem xSegsSVia_isSome_of_stratumA (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {P Q : Expr Nat} (s : Segs R Γ P Q)
    (hadm : s.admW = true) (hsA : s.stratumA = true)
    {A B A' B' : Expr Nat} (hP : P = .pi A B) (hQ : Q = .pi A' B') :
    (xSegsSVia X hΓ s hadm hP hQ).isSome = true :=
  xSegsViaS_isSome_of_stratumA (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) s hadm hsA hP hQ

/-- Stratum A is answered by every Via bundle (nothing here is
    vacuous). -/
theorem xValleySVia?_isSome_of_piSpined (X : SuppliersVia E n)
    (hΓ : CtxWfT E n Γ) {A B A' B' : Expr Nat}
    (c : EvTc R Γ (.pi A B) (.pi A' B')) (hp : piSpinedTc c = true) :
    (xValleySVia? X hΓ c
      (xAdmW_of_xAdm c (xAdm_of_piSpined c hp))).isSome = true :=
  xValleySViaS?_isSome_of_piSpined (X.atSeg hΓ) (JProcViaP.toViaSP X.J)
    (JContractViaP.toViaSP X.hJ) (.ofWf hΓ) c hp

/-! ### §5 teeth -/

/-- an insertion grows the length. -/
theorem insertAt_length (d : LocalDecl) : (k : Nat) → (Γ : LCtx) →
    (insertAt d k Γ).length = Γ.length + 1
  | 0, _ => rfl
  | _+1, [] => rfl
  | c+1, _ :: Γ => by
      simp only [insertAt, List.length_cons, insertAt_length d c Γ]

/-- a weakening only grows the context. -/
theorem Wk.length_le : {Γ₀ Γ' : LCtx} → Wk Γ₀ Γ' →
    Γ₀.length ≤ Γ'.length
  | _, _, .id _ => Nat.le_refl _
  | Γ₀, _, .ins d k ρ => by
      have h₁ := insertAt_length d k Γ₀
      have h₂ := Wk.length_le ρ
      omega

/-- Q3: WK-1's morphism class cannot cross a substitution link — a
    weakening never maps a context onto its own tail (insertion grows
    the length). -/
theorem no_wk_to_tail (x : LocalDecl) (Γ : LCtx) :
    ¬ Nonempty (Wk (x :: Γ) Γ) := by
  rintro ⟨ρ⟩
  have h := Wk.length_le ρ
  simp only [List.length_cons] at h
  omega

/-- so the inner context of an `esub 0` link (`x :: Γ`, outer
    `substRemove v 0 (x :: Γ) = Γ`) has no WK-1 Via witness built from
    the outer context's well-formedness: the worker's refusal of `esub`
    (`bCvW_esub`) is forced, not chosen; WK-2's typed `sub` arm (PR-A's
    `CtxMorph.sub`, #7148) is what admits it. -/
theorem no_via_across_esub0 (x : LocalDecl) (Γ : LCtx) :
    ¬ ∃ v : CtxWfVia E n (x :: Γ), v.target = Γ := by
  rintro ⟨v, hv⟩
  have hle := Wk.length_le v.ρ
  rw [hv, List.length_cons] at hle
  exact Nat.not_succ_le_self _ hle

/-- MUTANT: the premise-forgetting `CtxWfViaMut` (WK-1a) crosses the
    substitution link untyped — the same mutant that accepts `illCtx`
    (`mutant_accepts_illCtx`): `instantiate 0 v` preserves sorts
    (`instantiate`'s `.sort` arm is `rfl`). -/
def mutant_crosses_esub0 (x : LocalDecl) (Γ : LCtx) (v : Expr Nat)
    (hΓ : CtxWfT E n Γ) : CtxWfViaMut E n (x :: Γ) :=
  ⟨Γ, instantiate 0 v, fun _ => rfl, hΓ⟩

/-- Q4: `hΓ` cannot be invented — not every context is well-formed. -/
theorem invent_hΓ_impossible :
    ¬ ∀ Γ : LCtx, Nonempty (CtxWfT emptyEnv 0 Γ) := by
  intro h
  obtain ⟨w⟩ := h XTileQ1.illCtx
  exact illCtx_no_via ⟨CtxWfVia.ofWf w⟩

/-! ### §6 pins -/

section Pins
open EtaKAnnot EtaKAnnot.Pins

/-- the weakening declaration of the pins: `x : Sort 0`. -/
def wkDecl : LocalDecl := .assumption (.sort .zero)

/-- the β fixture under a cutoff-1 weakening over a nonempty context:
    `insertAt wkDecl 1 (insertAt wkDecl 0 []) = [wkDecl, wkDecl]` and
    `lift 1 1 piX = piX` (piX is closed), both `rfl`. -/
def pinWkInput : EvTc [Jd.tc betaMiddleT] [wkDecl, wkDecl] piX piX :=
  EvTc.wk wkDecl 1 (EvTc.wk wkDecl 0
    (EvTc.lit betaMiddleT ⟨.tc betaMiddleT, .head _, .inl rfl⟩))

/-- `[wkDecl, wkDecl]` is well-formed. -/
def pinWkCtxWf : CtxWfT emptyEnv 0 [wkDecl, wkDecl] :=
  .assumption _ _ _ (.assumption _ _ _ .nil (.sort _ .zero))
    (.sort _ .zero)

/-- W-X-WK today (the landed negative control's content): the β fixture
    under a cutoff-1 weakening is inadmissible to the landed route — the
    outer weakening is at cutoff 1, `bLink` refuses. -/
theorem pin_wk_xAdm_false : xAdm pinWkInput = false := by
  simp only [xAdm, pinWkInput, betaMiddleT, flattenTc, flattenT,
    Flat.append, Flat.wk, Flat.segment, Flat.segmentF, Flat.length,
    Flat.splitPi, Segs.adm, Flat.segAdm, Flat.bPrefix, bLink, bCv,
    isPi_lift, isPi, Bool.false_and, Bool.and_false, Bool.and_self,
    Bool.and_true, Bool.true_and]

/-- the same input is admitted by WK-1b's W fragment. -/
theorem pin_wk_xAdmW_true : xAdmW pinWkInput = true := by
  simp only [xAdmW, pinWkInput, betaMiddleT, flattenTc, flattenT,
    Flat.append, Flat.wk, Flat.segment, Flat.segmentF, Flat.length,
    Flat.splitPi, Segs.admW, Flat.segAdmW, Flat.bPrefixW, bLinkW, bCvW,
    Bool.and_self, Bool.and_true, Bool.true_and]

/-- every answer of the Via route on it has a lex census, for ANY
    bundle. -/
theorem pin_wk_edges (X : SuppliersVia emptyEnv 0) (r)
    (hr : xValleySVia? X pinWkCtxWf pinWkInput pin_wk_xAdmW_true = some r)
    (Z : List (Jd emptyEnv 0)) : EdgeContractLex (census pinWkInput r Z) :=
  xValleySVia_edges X pinWkCtxWf _ pin_wk_xAdmW_true r hr Z

/-- the Via witness the worker hands J for the inner `[]` literals of
    `pinWkInput`: not an `ofWf` — a two-insertion morphism matching the
    EvTc nesting (`wk` at cutoff 0, then at cutoff 1) with identity
    action on the closed `piX`. -/
def pinWkVia : CtxWfVia emptyEnv 0 [] :=
  ⟨[wkDecl, wkDecl], .ins wkDecl 0 (.ins wkDecl 1 (.id [wkDecl, wkDecl])),
    pinWkCtxWf⟩

/-- its action on the closed `piX` is the identity. -/
theorem pinWkVia_map : pinWkVia.ρ.map piX = piX := rfl

/-- the declining bundle refuses the weakened β segment as a SUPPLIER
    refusal (J declines at the literal), not an admissibility refusal —
    the same segment as `pin_betaTwoLinks_declined`, carried under the
    two `wk`s, still admissible (`by decide`) to the W fragment. -/
theorem pin_wk_declined (hsep : SepAll emptyEnv 0) :
    xSegsSVia (SuppliersVia.declining hsep) pinWkCtxWf
      (Segs.cons ((betaTwoLinks.wk wkDecl 0).wk wkDecl 1) rfl
        (Segs.nil piX)) (by decide) rfl rfl = none := rfl

/-- the `request` fixture stays Π-spined under a cutoff-1 weakening:
    `isPi` of its (closed, twice-lifted) endpoints. -/
private theorem pinWkRequestSpined :
    piSpinedTc (EvTc.wk wkDecl 1 (EvTc.wk wkDecl 0 request)) = true := by
  simp only [piSpinedTc, piSpinedT, piSpinedConv, isPi, isPi_lift, lift,
    request, annotRequest, cL, cR, piConversion, piL, piR, Bool.and_self,
    Bool.true_and, Bool.and_true]

/-- Stratum A under a cutoff-1 weakening still answers through the Via
    route for every bundle. -/
theorem pin_wk_request_answered (hsep : SepAll emptyEnv 0) :
    (xValleySVia? (SuppliersVia.declining hsep) pinWkCtxWf
      (EvTc.wk wkDecl 1 (EvTc.wk wkDecl 0 request))
      (xAdmW_of_xAdm _ (xAdm_of_piSpined _ pinWkRequestSpined))).isSome =
        true :=
  xValleySVia?_isSome_of_piSpined _ _ _ pinWkRequestSpined

/-! #### source/segment-distinguishing S controls (audit P2)

An S supplier that answers ONLY at the segment context `[wkDecl, wkDecl]`
(`sSeg`) and one that answers ONLY at the source `[]` (`sSrc`). Reading
the deep-thinned fixture valley, the segment-only supplier is reached
(the steps sit at `Γ'`); the source-only supplier is never asked. Under
the OLD lazy thinning the reader descends to the source star and the
source-only supplier answers — `pin_read_lazy_src` keeps that behaviour
pinned as the negative control. -/

/-- the segment-only S: `structPiSelf` answers `.structPi` steps only at
    `[wkDecl, wkDecl]`, and declines everywhere else. -/
def sSeg : ∀ R : List (Jd emptyEnv 0), StructPiProcP R :=
  fun R {Γ} {_ _ _ _} s =>
    match s with
    | .structPi p =>
        if Γ = [wkDecl, wkDecl] then some (structPiSelf p) else none
    | _ => none

/-- the source-only S: `structPiSelf` answers `.structPi` steps only at
    `[]`, and declines everywhere else. -/
def sSrc : ∀ R : List (Jd emptyEnv 0), StructPiProcP R :=
  fun R {Γ} {_ _ _ _} s =>
    match s with
    | .structPi p => if Γ = [] then some (structPiSelf p) else none
    | _ => none

theorem sSeg_contract : StructPiContractP sSeg := by
  intro R Γ A B q T s r hr
  cases s with
  | structPi p =>
      have h' : (if Γ = [wkDecl, wkDecl] then some (structPiSelf p)
          else none) = some r := hr
      split at h'
      · next _ =>
          obtain rfl := Option.some.inj h'
          exact structPiSelf_contract p
      · next _ => exact Option.noConfusion h'
  | proofIndex _ => exact Option.noConfusion hr
  | refl _ => exact Option.noConfusion hr

theorem sSrc_contract : StructPiContractP sSrc := by
  intro R Γ A B q T s r hr
  cases s with
  | structPi p =>
      have h' : (if Γ = [] then some (structPiSelf p) else none) =
          some r := hr
      split at h'
      · next _ =>
          obtain rfl := Option.some.inj h'
          exact structPiSelf_contract p
      · next _ => exact Option.noConfusion h'
  | proofIndex _ => exact Option.noConfusion hr
  | refl _ => exact Option.noConfusion hr

/-- `piX` typed at its own sort — the landed `pinPiT` fixture. -/
def pinPiTy : HasTyT emptyEnv 0 [] piX sX := pinPiT emptyEnv 0

/-- the root bundle of the S-control fixture: just `piX`'s typing. -/
def pinPiR : List (Jd emptyEnv 0) := [.ty pinPiTy]

/-- `pinPiTy` as provenance — the fixture's only leaf. -/
def pinHrt : EvTy pinPiR [] piX sX :=
  .lit pinPiTy ⟨_, .head _, .inl rfl⟩

/-- a self-structural-Π payload for `piX`: `piX` steps to `piX` by its
    own data — `u = v = 1`, both domain fields `Sort 0 : Sort 1`, the
    target typing `pinHrt`, and the index `sX ≡ sX` by `refl` (sX IS
    `sort (imax 1 1)`). -/
def pinSelfPayload : StructPiPayload pinPiR [] (.sort .zero) (.sort .zero)
    (.sort .zero) (.sort .zero) sX where
  u := .succ .zero
  v := .succ .zero
  hA := .sort .zero
  hc := .refl (.sort .zero)
  hB := .sort .zero
  hcB := .refl (.sort .zero)
  hrt := pinHrt
  idx := .refl _ _

/-- a one-step valley at `[]`: the left leg is the self `structPi` step
    then `refl`, the right leg is `refl`. The only leaf is `pinHrt`'s,
    sitting inside the structural payload's `hrt`. -/
def pinSelfValley : Valley pinPiR [] piX piX sX where
  N := piX
  left := .tail (.structPi pinSelfPayload) (.refl pinHrt)
  right := .refl pinHrt
  ty₁ := pinHrt
  ty₂ := pinHrt

/-- the two-insertion morphism `[] → [wkDecl, wkDecl]` — the same shape
    as `pinWkVia.ρ`, as a bare `Wk`. -/
def pinρ : Wk [] [wkDecl, wkDecl] :=
  .ins wkDecl 0 (.ins wkDecl 1 (.id _))

/-- the `viaS` route on the pin's `ofWf` witness builds exactly the
    `toCtxMorph` stack the WK-1a witness `pinWkVia` carries —
    `.ins wkDecl 0 (.ins wkDecl 1 .nil)`, not an identity: J is invoked
    at a genuine two-insertion `CtxMorph`. -/
theorem pin_viaS_witness :
    (pinρ.viaS (.ofWf pinWkCtxWf)).σ = pinρ.toCtxMorph :=
  eq_of_heq (Wk.viaS_σ pinρ pinWkCtxWf)

/-- the Via bundle with `sSeg` as S (K/J/D/U declining). -/
def XSeg (hsep : SepAll emptyEnv 0) : SuppliersVia emptyEnv 0 :=
  { SuppliersVia.declining hsep with S := sSeg, hS := sSeg_contract }

/-- the Via bundle with `sSrc` as S. -/
def XSrc (hsep : SepAll emptyEnv 0) : SuppliersVia emptyEnv 0 :=
  { SuppliersVia.declining hsep with S := sSrc, hS := sSrc_contract }

/-- CONTROL 1 (the fix): deep thinning puts the `structPi` step at the
    segment context — the segment-only S answers. -/
theorem pin_read_deep_seg (hsep : SepAll emptyEnv 0) :
    (readValleyC ((XSeg hsep).atSeg pinWkCtxWf)
      (pinSelfValley.thinDeep pinρ)).isSome = true := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [readValleyC, readStarC, ValleyOps.readValleyC, ValleyOps.readStarC,
    Suppliers.toValleyOps, reduceAnd, pinSelfValley,
    Valley.thinDeep, EvParStar.thinDeep, EvPar.thin, EvPar.wk,
    StructPiPayload.wk, ProofIndexPayload.wk, SortEqPayload.wk,
    ConstsPayload.wk, LitPayload.wk, Wk.map, insertAt, lift,
    SuppliersVia.atSeg, XSeg, SuppliersVia.declining, sSeg,
    structPiSelf, pinHrt, pinSelfPayload, pinPiTy, pinPiR, wkDecl]

/-- CONTROL 2: the source-only S is never asked — the deep-thinned
    valley's step is not at `[]`, so the read refuses. -/
theorem pin_read_deep_src (hsep : SepAll emptyEnv 0) :
    (readValleyC ((XSrc hsep).atSeg pinWkCtxWf)
      (pinSelfValley.thinDeep pinρ)).isSome = false := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [readValleyC, readStarC, ValleyOps.readValleyC, ValleyOps.readStarC,
    Suppliers.toValleyOps, reduceAnd, pinSelfValley,
    Valley.thinDeep, EvParStar.thinDeep, EvPar.thin, EvPar.wk,
    StructPiPayload.wk, ProofIndexPayload.wk, SortEqPayload.wk,
    ConstsPayload.wk, LitPayload.wk, Wk.map, insertAt, lift,
    SuppliersVia.atSeg, XSrc, SuppliersVia.declining, sSrc,
    structPiSelf, pinHrt, pinSelfPayload, pinPiTy, pinPiR, wkDecl]

/-- CONTROL 3 (the refused behaviour, kept as the negative control):
    under LAZY `Valley.thin` the inherited reader unwraps the `wk` nodes
    and descends to the source star — the source-only S answers. This is
    what the refused head did. -/
theorem pin_read_lazy_src (hsep : SepAll emptyEnv 0) :
    (readValleyC ((XSrc hsep).atSeg pinWkCtxWf)
      (pinSelfValley.thin pinρ)).isSome = true := by
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [readValleyC, readStarC, ValleyOps.readValleyC, ValleyOps.readStarC,
    Suppliers.toValleyOps, reduceAnd, pinSelfValley,
    Valley.thin, Valley.wk, EvParStar.thinDeep, EvPar.thin, EvPar.wk,
    StructPiPayload.wk, ProofIndexPayload.wk, SortEqPayload.wk,
    ConstsPayload.wk, LitPayload.wk, Wk.map, insertAt, lift,
    SuppliersVia.atSeg, XSrc, SuppliersVia.declining, sSrc,
    structPiSelf, pinHrt, pinSelfPayload, pinPiTy, pinPiR, wkDecl]

/-! #### Q92 — refuse a weakened-then-substituted returned star

The audit's control: `pinSelfValley`, weakened by one dummy assumption
(`sort 1`), then `subst0`'d away by the intrinsic `sort 0 : sort 1`.
The closed Π endpoints and the original typing leaves survive. Applying
`pinρ` leaves the lazy `wk` wrappers OUTSIDE the substitution, so the
inherited reader would call the source-only S. The lit arm now refuses
that valley before `readStarC`. The mutant is `admitSubst false` — the
same gate with only the refusal deleted — and the reader then accepts. -/

/-- one dummy assumption of `Sort 1`. -/
def pinQ92Dummy : LocalDecl := .assumption (.sort (.succ .zero))

/-- the real request the leaves sit under: `refl` of `piX : sX`. -/
def pinQ92Cv : ConvT emptyEnv 0 [] piX piX sX :=
  .refl [] piX sX pinPiTy

/-- `pinPiR` widened by that request, so the lit's membership is real. -/
def pinQ92R : List (Jd emptyEnv 0) := pinPiR ++ [.cv pinQ92Cv]

/-- `sort 0 : sort 1` at the context substitution returns to. -/
def pinQ92Hv : EvTy pinQ92R [] (.sort .zero) (.sort (.succ .zero)) :=
  .sort .zero

/-- `.ty pinPiTy` sits in `pinPiR`, hence in the widened bundle. -/
theorem pinQ92TyMem : Jd.ty pinPiTy ∈ pinQ92R := by
  unfold pinQ92R pinPiR
  exact List.mem_append.mpr (Or.inl (List.Mem.head _))

/-- `pinHrt` on the widened bundle. The leaf is still `.ty pinPiTy`. -/
def pinQ92Hrt : EvTy pinQ92R [] piX sX :=
  .lit pinPiTy ⟨Jd.ty pinPiTy, pinQ92TyMem, Or.inl rfl⟩

/-- `pinSelfPayload` on the widened bundle. -/
def pinQ92Payload : StructPiPayload pinQ92R [] (.sort .zero) (.sort .zero)
    (.sort .zero) (.sort .zero) sX where
  u := .succ .zero
  v := .succ .zero
  hA := .sort .zero
  hc := .refl (.sort .zero)
  hB := .sort .zero
  hcB := .refl (.sort .zero)
  hrt := pinQ92Hrt
  idx := .refl _ _

/-- `pinSelfValley` on the widened bundle, still at `[]`. -/
def pinQ92Base : Valley pinQ92R [] piX piX sX where
  N := piX
  left := .tail (.structPi pinQ92Payload) (.refl pinQ92Hrt)
  right := .refl pinQ92Hrt
  ty₁ := pinQ92Hrt
  ty₂ := pinQ92Hrt

/-- weaken by one dummy assumption, then `subst0` it away. Endpoints
    stay the closed `piX`. -/
def pinQ92Valley : Valley pinQ92R [] piX piX sX :=
  (pinQ92Base.wk pinQ92Dummy 0).subst0 (t := .sort (.succ .zero))
    (v := .sort .zero) 0 rfl pinQ92Hv

theorem pinQ92Valley_leaves :
    pinQ92Valley.leaves =
      [.ty pinPiTy, .ty pinPiTy, .ty pinPiTy, .ty pinPiTy, .ty pinPiTy] :=
  rfl

/-- `.cv pinQ92Cv` is the second entry of the widened bundle. -/
theorem pinQ92CvMem : Jd.cv pinQ92Cv ∈ pinQ92R := by
  unfold pinQ92R
  exact List.mem_append.mpr (Or.inr (List.Mem.head _))

/-- the lit the Via worker is handed for this control. -/
def pinQ92Ev : EvCv pinQ92R [] piX piX sX :=
  .lit pinQ92Cv ⟨Jd.cv pinQ92Cv, pinQ92CvMem, Or.inl rfl⟩

/-- `pinPiTy` written as constructors. Reduces to `pinPiTy`. -/
private abbrev pinQ92Ht : HasTyT emptyEnv 0 [] piX sX :=
  .pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
    (.sort [] .zero) (.sort [.assumption (.sort .zero)] .zero)

private theorem pinQ92Ht_eq : pinQ92Ht = pinPiTy := rfl

/-- J's answer packed with the leaf contract. The contract theorem
    projects that proof and does not unfold the matcher on a symbolic
    conv. The success arm is constructors only, so on the audit's
    request it reduces to `some pinQ92Valley`. -/
private def jQ92Packed (R : List (Jd emptyEnv 0)) {Γ₀ : LCtx} {M₁ M₂ T : Expr Nat}
    (_v : CtxWfVia emptyEnv 0 Γ₀) (h : ConvT emptyEnv 0 Γ₀ M₁ M₂ T)
    (_hs : ∃ r ∈ R, SubEq (.cv h) r) :
    Option {V : Valley R Γ₀ M₁ M₂ T // ∀ ℓ ∈ V.leaves, SubOf ℓ (.cv h)} :=
  match h with
  | ConvT.refl Γ a A ht =>
      match Γ, a, A, ht, R with
      | [], .pi (.sort .zero) (.sort .zero),
        .sort (.imax (.succ .zero) (.succ .zero)),
        HasTyT.pi [] (.sort .zero) (.succ .zero) (.sort .zero) (.succ .zero)
          (HasTyT.sort [] .zero)
          (HasTyT.sort [.assumption (.sort .zero)] .zero),
        [Jd.ty (HasTyT.pi [] (.sort .zero) (.succ .zero) (.sort .zero)
            (.succ .zero) (HasTyT.sort [] .zero)
            (HasTyT.sort [.assumption (.sort .zero)] .zero)),
         Jd.cv (ConvT.refl [] (.pi (.sort .zero) (.sort .zero))
            (.sort (.imax (.succ .zero) (.succ .zero)))
            (HasTyT.pi [] (.sort .zero) (.succ .zero) (.sort .zero)
              (.succ .zero) (HasTyT.sort [] .zero)
              (HasTyT.sort [.assumption (.sort .zero)] .zero)))] =>
          some ⟨pinQ92Valley, by
            intro ℓ hℓ
            have hℓ' : ℓ = .ty pinPiTy := by
              simpa [pinQ92Valley_leaves, pinQ92Ht_eq, List.mem_cons,
                List.not_mem_nil, or_false] using hℓ
            subst hℓ'
            exact SubOf.child (by
              simp only [Child, Jd.children, Jd.cvChildren]
              exact List.Mem.head _)⟩
      | _, _, _, _, _ => none
  | _ => none

def jQ92 : ∀ R : List (Jd emptyEnv 0), JProcViaP (E := emptyEnv) (n := 0) R :=
  fun R {_ _ _ _} v h hs => (jQ92Packed R v h hs).map Subtype.val

theorem jQ92_contract : JContractViaP (E := emptyEnv) (n := 0) jQ92 := by
  intro R Γ₀ M₁ M₂ T v h hsub V hV
  simp only [jQ92] at hV
  obtain ⟨W, _, rfl⟩ := Option.map_eq_some'.mp hV
  exact W.property

/-- the Via bundle whose J returns the Q92 control. -/
def XQ92 (hsep : SepAll emptyEnv 0) : SuppliersVia emptyEnv 0 :=
  { SuppliersVia.declining hsep with J := jQ92, hJ := jQ92_contract }

/-- J returns the audit control, so the refusal is not a declined supplier. -/
theorem pin_q92_j_returns :
    jQ92 pinQ92R ⟨[wkDecl, wkDecl], pinρ, pinWkCtxWf⟩ pinQ92Cv
      ⟨Jd.cv pinQ92Cv, pinQ92CvMem, Or.inl rfl⟩ = some pinQ92Valley := rfl

/-- the gate itself drops this valley. `admitSubst false` is the mutant. -/
theorem pin_q92_gate_refuses :
    Valley.admitSubst true pinQ92Valley = none := rfl

/-- the real accept path refuses the weaken-then-`subst0` control
    before the inherited reader runs. -/
theorem pin_q92_weaken_subst0_refused (hsep : SepAll emptyEnv 0) :
    svalleyCvVia (XQ92 hsep) pinQ92Ev pinρ pinWkCtxWf rfl = none := rfl

/-- MUTANT: delete only the refusal (`admitSubst false`). The same
    control is handed on, and the inherited reader accepts it — the
    source-only S answers, which is the segment-context break. -/
theorem pin_q92_weaken_subst0_mutant_accepts (hsep : SepAll emptyEnv 0) :
    Valley.admitSubst false pinQ92Valley = some pinQ92Valley ∧
      (readValleyC ((XSrc hsep).atSeg pinWkCtxWf)
        (pinQ92Valley.thinDeep pinρ)).isSome = true := by
  refine ⟨rfl, ?_⟩
  have reduceAnd {p q : Prop} {m : p ∧ q → Type}
      (f : (hp : p) → (hq : q) → m ⟨hp, hq⟩) (h : p ∧ q) :
      And.rec (motive := m) f h = f h.1 h.2 := by cases h; rfl
  simp [readValleyC, readStarC, ValleyOps.readValleyC, ValleyOps.readStarC,
    Suppliers.toValleyOps, reduceAnd, isPiD, instShape_pi, isPi, isPi_lift,
    pinQ92Valley, pinQ92Base, pinQ92Payload, pinQ92Hrt, pinQ92Hv, pinQ92Dummy,
    pinQ92R, pinQ92Cv, Valley.thinDeep, Valley.wk, Valley.subst0,
    EvParStar.thinDeep, EvParStar.thinWk, EvParStar.wk, EvParStar.subst0,
    EvTy.wk, EvTy.subst0, EvTy.sort, EvPar.thin, EvPar.wk, StructPiPayload.wk,
    ProofIndexPayload.wk, SortEqPayload.wk, ConstsPayload.wk, LitPayload.wk,
    Wk.map, insertAt, lift, instantiate, substRemove, SuppliersVia.atSeg,
    XSrc, SuppliersVia.declining, sSrc, structPiSelf, pinPiTy, pinPiR,
    pinρ, wkDecl]

end Pins

end Rcic.Declarative.F8Measure

#print axioms Rcic.Declarative.F8Measure.EvTy.thin
#print axioms Rcic.Declarative.F8Measure.EvTc.thin
#print axioms Rcic.Declarative.F8Measure.EvCv.thin
#print axioms Rcic.Declarative.F8Measure.Valley.thin
#print axioms Rcic.Declarative.F8Measure.SRes.thin
#print axioms Rcic.Declarative.F8Measure.SOut.thin
#print axioms Rcic.Declarative.F8Measure.EvTy.thin_leaves
#print axioms Rcic.Declarative.F8Measure.EvTc.thin_leaves
#print axioms Rcic.Declarative.F8Measure.EvCv.thin_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.thin_leaves
#print axioms Rcic.Declarative.F8Measure.SRes.thin_leaves
#print axioms Rcic.Declarative.F8Measure.SRes.thin_pendingLeaves
#print axioms Rcic.Declarative.F8Measure.SRes.thin_isVal
#print axioms Rcic.Declarative.F8Measure.SOut.bound_thin
#print axioms Rcic.Declarative.F8Measure.bCvW
#print axioms Rcic.Declarative.F8Measure.bLinkW
#print axioms Rcic.Declarative.F8Measure.Flat.bPrefixW
#print axioms Rcic.Declarative.F8Measure.Flat.segAdmW
#print axioms Rcic.Declarative.F8Measure.Segs.admW
#print axioms Rcic.Declarative.F8Measure.xAdmW
#print axioms Rcic.Declarative.F8Measure.bCvW_of_bCv
#print axioms Rcic.Declarative.F8Measure.bLinkW_of_bLink
#print axioms Rcic.Declarative.F8Measure.Flat.bPrefixW_of_bPrefix
#print axioms Rcic.Declarative.F8Measure.Flat.segAdmW_of_segAdm
#print axioms Rcic.Declarative.F8Measure.Segs.admW_of_adm
#print axioms Rcic.Declarative.F8Measure.xAdmW_of_xAdm
#print axioms Rcic.Declarative.F8Measure.bLinkW_wk
#print axioms Rcic.Declarative.F8Measure.bCvW_esub
#print axioms Rcic.Declarative.F8Measure.DProcWfP
#print axioms Rcic.Declarative.F8Measure.DContractWfP
#print axioms Rcic.Declarative.F8Measure.DProcWfP.ofTotal
#print axioms Rcic.Declarative.F8Measure.DContractWfP.ofTotal
#print axioms Rcic.Declarative.F8Measure.DProcWfP.ofTotal_eq
#print axioms Rcic.Declarative.F8Measure.DProcP.toWfP
#print axioms Rcic.Declarative.F8Measure.DContractP.toWfP
#print axioms Rcic.Declarative.F8Measure.d1WfP
#print axioms Rcic.Declarative.F8Measure.d1WfP_contract
#print axioms Rcic.Declarative.F8Measure.SuppliersVia
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.atSeg
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.atSeg_D_eq
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.atSeg_D_ne
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.declining
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.withJ
#print axioms Rcic.Declarative.F8Measure.svalleyCvVia
#print axioms Rcic.Declarative.F8Measure.slinkValleyVia
#print axioms Rcic.Declarative.F8Measure.sprefixValleyVia
#print axioms Rcic.Declarative.F8Measure.xSegSVia
#print axioms Rcic.Declarative.F8Measure.xSegsSVia
#print axioms Rcic.Declarative.F8Measure.xValleySVia?
#print axioms Rcic.Declarative.F8Measure.xValleySVia_contract
#print axioms Rcic.Declarative.F8Measure.xValleySVia_edges
#print axioms Rcic.Declarative.F8Measure.xSegSVia_isSome_of_spined
#print axioms Rcic.Declarative.F8Measure.xSegsSVia_isSome_of_stratumA
#print axioms Rcic.Declarative.F8Measure.xValleySVia?_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.insertAt_length
#print axioms Rcic.Declarative.F8Measure.Wk.length_le
#print axioms Rcic.Declarative.F8Measure.no_wk_to_tail
#print axioms Rcic.Declarative.F8Measure.no_via_across_esub0
#print axioms Rcic.Declarative.F8Measure.mutant_crosses_esub0
#print axioms Rcic.Declarative.F8Measure.invent_hΓ_impossible
#print axioms Rcic.Declarative.F8Measure.wkDecl
#print axioms Rcic.Declarative.F8Measure.pinWkInput
#print axioms Rcic.Declarative.F8Measure.pinWkCtxWf
#print axioms Rcic.Declarative.F8Measure.pin_wk_xAdm_false
#print axioms Rcic.Declarative.F8Measure.pin_wk_xAdmW_true
#print axioms Rcic.Declarative.F8Measure.pin_wk_edges
#print axioms Rcic.Declarative.F8Measure.pinWkVia
#print axioms Rcic.Declarative.F8Measure.pinWkVia_map
#print axioms Rcic.Declarative.F8Measure.pin_wk_declined
#print axioms Rcic.Declarative.F8Measure.pin_wk_request_answered
#print axioms Rcic.Declarative.F8Measure.EvPar.cast
#print axioms Rcic.Declarative.F8Measure.EvPar.cast_leaves
#print axioms Rcic.Declarative.F8Measure.ProofIndexPayload.wk
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.wk
#print axioms Rcic.Declarative.F8Measure.SortEqPayload.wk
#print axioms Rcic.Declarative.F8Measure.ConstsPayload.wk
#print axioms Rcic.Declarative.F8Measure.LitPayload.wk
#print axioms Rcic.Declarative.F8Measure.ProofIndexPayload.wk_leaves
#print axioms Rcic.Declarative.F8Measure.StructPiPayload.wk_leaves
#print axioms Rcic.Declarative.F8Measure.SortEqPayload.wk_leaves
#print axioms Rcic.Declarative.F8Measure.ConstsPayload.wk_leaves
#print axioms Rcic.Declarative.F8Measure.LitPayload.wk_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.wk
#print axioms Rcic.Declarative.F8Measure.EvPar.wk_leaves
#print axioms Rcic.Declarative.F8Measure.EvPar.thin
#print axioms Rcic.Declarative.F8Measure.EvPar.thin_leaves
#print axioms Rcic.Declarative.F8Measure.EvParStar.thinDeep
#print axioms Rcic.Declarative.F8Measure.EvParStar.thinDeep_leaves
#print axioms Rcic.Declarative.F8Measure.Valley.thinDeep
#print axioms Rcic.Declarative.F8Measure.Valley.thinDeep_leaves
#print axioms Rcic.Declarative.F8Measure.sSeg
#print axioms Rcic.Declarative.F8Measure.sSrc
#print axioms Rcic.Declarative.F8Measure.sSeg_contract
#print axioms Rcic.Declarative.F8Measure.sSrc_contract
#print axioms Rcic.Declarative.F8Measure.pinPiTy
#print axioms Rcic.Declarative.F8Measure.pinPiR
#print axioms Rcic.Declarative.F8Measure.pinHrt
#print axioms Rcic.Declarative.F8Measure.pinSelfPayload
#print axioms Rcic.Declarative.F8Measure.pinSelfValley
#print axioms Rcic.Declarative.F8Measure.pinρ
#print axioms Rcic.Declarative.F8Measure.XSeg
#print axioms Rcic.Declarative.F8Measure.XSrc
#print axioms Rcic.Declarative.F8Measure.pin_read_deep_seg
#print axioms Rcic.Declarative.F8Measure.pin_read_deep_src
#print axioms Rcic.Declarative.F8Measure.pin_read_lazy_src
#print axioms Rcic.Declarative.CtxMorph.toWk?
#print axioms Rcic.Declarative.F8Measure.Wk.toCtxMorph_toWk?
#print axioms Rcic.Declarative.F8Measure.Wk.viaS
#print axioms Rcic.Declarative.F8Measure.Wk.viaS_ofWf
#print axioms Rcic.Declarative.F8Measure.Wk.viaS_σ
#print axioms Rcic.Declarative.F8Measure.JProcViaP.toViaSP
#print axioms Rcic.Declarative.F8Measure.JContractViaP.toViaSP
#print axioms Rcic.Declarative.F8Measure.JProcViaP.toViaSP_sub_none
#print axioms Rcic.Declarative.F8Measure.JProcViaP.toViaSP_viaS
#print axioms Rcic.Declarative.F8Measure.svalleyCvViaS
#print axioms Rcic.Declarative.F8Measure.svalleyCvVia_eq
#print axioms Rcic.Declarative.F8Measure.slinkValleyViaS
#print axioms Rcic.Declarative.F8Measure.slinkValleyVia_eq
#print axioms Rcic.Declarative.F8Measure.sprefixValleyViaS
#print axioms Rcic.Declarative.F8Measure.sprefixValleyVia_eq
#print axioms Rcic.Declarative.F8Measure.xSegSViaS
#print axioms Rcic.Declarative.F8Measure.xSegSVia_eq
#print axioms Rcic.Declarative.F8Measure.xSegsViaS
#print axioms Rcic.Declarative.F8Measure.xSegsSVia_eq
#print axioms Rcic.Declarative.F8Measure.xValleySViaS?
#print axioms Rcic.Declarative.F8Measure.xValleySVia?_eq
#print axioms Rcic.Declarative.F8Measure.xValleySViaS_contract
#print axioms Rcic.Declarative.F8Measure.xValleySViaS_edges
#print axioms Rcic.Declarative.F8Measure.xSegSViaS_isSome_of_spined
#print axioms Rcic.Declarative.F8Measure.xSegsViaS_isSome_of_stratumA
#print axioms Rcic.Declarative.F8Measure.xValleySViaS?_isSome_of_piSpined
#print axioms Rcic.Declarative.F8Measure.pin_viaS_witness
#print axioms Rcic.Declarative.F8Measure.EvParStar.hasSubst
#print axioms Rcic.Declarative.F8Measure.Valley.hasSubst
#print axioms Rcic.Declarative.F8Measure.Valley.admitSubst
#print axioms Rcic.Declarative.F8Measure.pinQ92Dummy
#print axioms Rcic.Declarative.F8Measure.pinQ92Cv
#print axioms Rcic.Declarative.F8Measure.pinQ92R
#print axioms Rcic.Declarative.F8Measure.pinQ92Hv
#print axioms Rcic.Declarative.F8Measure.pinQ92TyMem
#print axioms Rcic.Declarative.F8Measure.pinQ92Hrt
#print axioms Rcic.Declarative.F8Measure.pinQ92Payload
#print axioms Rcic.Declarative.F8Measure.pinQ92Base
#print axioms Rcic.Declarative.F8Measure.pinQ92Valley
#print axioms Rcic.Declarative.F8Measure.pinQ92Valley_leaves
#print axioms Rcic.Declarative.F8Measure.pinQ92CvMem
#print axioms Rcic.Declarative.F8Measure.pinQ92Ev
#print axioms Rcic.Declarative.F8Measure.jQ92
#print axioms Rcic.Declarative.F8Measure.jQ92_contract
#print axioms Rcic.Declarative.F8Measure.XQ92
#print axioms Rcic.Declarative.F8Measure.pin_q92_j_returns
#print axioms Rcic.Declarative.F8Measure.pin_q92_gate_refuses
#print axioms Rcic.Declarative.F8Measure.pin_q92_weaken_subst0_refused
#print axioms Rcic.Declarative.F8Measure.pin_q92_weaken_subst0_mutant_accepts

#print axioms Rcic.Declarative.F8Measure.ViaSCore.atOps
#print axioms Rcic.Declarative.F8Measure.SuppliersVia.core

#print axioms Rcic.Declarative.F8Measure.Suppliers.structRunnerViaS
